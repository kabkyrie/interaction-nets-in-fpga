module Tests.Isomorphism.Check (
  Mismatch (..),
  Side (..),
  checkIsomorphism,
  checkFrom,
  isIsomorphic,
) where

import Clash.Prelude (KnownNat)
import Control.Monad (foldM, unless)
import Core.Node (AddressNumber, Node (..), Port (..))
import Data.Bifunctor (first)
import Data.Either (partitionEithers)
import qualified Data.Map.Strict as M
import Tests.Isomorphism.NetSnapshot (NetSnapshot (..), slots)
import Prelude

data Side = FirstNet | SecondNet
  deriving (Eq, Show)

data Mismatch
  = NoStartNode
  | MissingNode Side AddressNumber
  | LabelMismatch AddressNumber AddressNumber
  | PortMismatch AddressNumber AddressNumber Int
  | MappingConflict AddressNumber AddressNumber
  | Disconnected Int Int Int
  deriving (Eq, Show)

data Failure = Failure Int Mismatch

progress :: Failure -> Int
progress (Failure matched _) = matched

reason :: Failure -> Mismatch
reason (Failure _ mismatch) = mismatch

data Matching = Matching
  { fwd :: M.Map AddressNumber AddressNumber
  , bwd :: M.Map AddressNumber AddressNumber
  }

bind :: Matching -> AddressNumber -> AddressNumber -> Either Mismatch (Maybe Matching)
bind m a b =
  case (M.lookup a (fwd m), M.lookup b (bwd m)) of
    (Nothing, Nothing) -> Right (Just (Matching (M.insert a b (fwd m)) (M.insert b a (bwd m))))
    (Just b', Just a') | b' == b && a' == a -> Right Nothing
    _ -> Left (MappingConflict a b)

portPairs ::
  (KnownNat p) =>
  AddressNumber ->
  AddressNumber ->
  Node p a ->
  Node p a ->
  Either Mismatch [(AddressNumber, AddressNumber)]
portPairs a b na nb = concat <$> sequence (zipWith3 one [0 :: Int ..] (slots na) (slots nb))
 where
  one i sa sb = case (sa, sb) of
    (Nothing, Nothing) -> Right []
    (Just Nothing, Just Nothing) -> Right []
    (Just (Just (Port x px)), Just (Just (Port y py)))
      | px == py -> Right [(x, y)]
    _ -> Left (PortMismatch a b i)

runFrom ::
  (KnownNat p, Eq a) =>
  [(AddressNumber, AddressNumber)] ->
  NetSnapshot p a ->
  NetSnapshot p a ->
  Either Failure ()
runFrom starts net1 net2 = do
  (m0, queue0) <- first (Failure 0) (foldM bindNew (Matching M.empty M.empty, []) starts)
  m <- go m0 queue0
  let n1 = M.size (snapNodes net1)
      n2 = M.size (snapNodes net2)
      matched = M.size (fwd m)
  unless (n1 == matched && n2 == matched) (Left (Failure matched (Disconnected n1 n2 matched)))
 where
  bindNew (m, queue) (a, b) = do
    r <- bind m a b
    pure $ case r of
      Nothing -> (m, queue)
      Just m' -> (m', (a, b) : queue)

  look side net addr =
    maybe (Left (MissingNode side addr)) Right (M.lookup addr (snapNodes net))

  step m a b = do
    na <- look FirstNet net1 a
    nb <- look SecondNet net2 b
    unless (_nodeType na == _nodeType nb) (Left (LabelMismatch a b))
    pairs <- portPairs a b na nb
    foldM bindNew (m, []) pairs

  go m [] = Right m
  go m ((a, b) : rest) =
    case step m a b of
      Left mismatch -> Left (Failure (M.size (fwd m)) mismatch)
      Right (m', new) -> go m' (new ++ rest)

checkFrom ::
  (KnownNat p, Eq a) =>
  [(AddressNumber, AddressNumber)] ->
  NetSnapshot p a ->
  NetSnapshot p a ->
  Either Mismatch ()
checkFrom starts net1 net2 = first reason (runFrom starts net1 net2)

freeSlots :: (KnownNat p) => Node p a -> [Int]
freeSlots n = [i | (i, Just Nothing) <- zip [0 ..] (slots n)]

startPairs ::
  (KnownNat p, Eq a) =>
  NetSnapshot p a -> NetSnapshot p a -> [(AddressNumber, AddressNumber)]
startPairs net1 net2 =
  case [(a, na, i) | (a, na) <- M.toList (snapNodes net1), i <- freeSlots na] of
    (a, na, i) : _ -> candidates a na (elem i . freeSlots)
    [] -> case M.lookupMin (snapNodes net1) of
      Just (a, na) -> candidates a na (const True)
      Nothing -> []
 where
  candidates a na ok =
    [(a, b) | (b, nb) <- M.toList (snapNodes net2), _nodeType nb == _nodeType na, ok nb]

checkIsomorphism ::
  (KnownNat p, Eq a) =>
  NetSnapshot p a -> NetSnapshot p a -> Either Mismatch ()
checkIsomorphism net1 net2
  | M.null (snapNodes net1) && M.null (snapNodes net2) = Right ()
  | otherwise =
      case partitionEithers (map (\start -> runFrom [start] net1 net2) (startPairs net1 net2)) of
        ([], []) -> Left NoStartNode
        (_, _ : _) -> Right ()
        (f : fs, []) -> Left (reason (foldl furthest f fs))
 where
  furthest best candidate = if progress candidate > progress best then candidate else best

isIsomorphic :: (KnownNat p, Eq a) => NetSnapshot p a -> NetSnapshot p a -> Bool
isIsomorphic net1 net2 = either (const False) (const True) (checkIsomorphism net1 net2)
