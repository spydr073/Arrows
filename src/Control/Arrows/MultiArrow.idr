
-----------------------------------------------------------------------------------------[ Module ]
--{1
--                                                                              (\_/)
--                                                                              (o.O)
--                                                                              (> <)
--                                                                             #######
--                                                                           KILLER BUNNY
--                                                                             APPROVED
--
-- Model finite functions that may not be surjective. This is achieved by using a finite mapping
-- from each element in the domain to a multiset of reachable elements in the codomain. Note that
-- as this module has been written, we get Arrow composition for free!

module Arrow

import Data.AA.Map
import Data.AA.Set.MultiSet      as  MSet
import Data.AA.Set.IndexMultiSet as IMSet

%default total
%access private

--}

---------------------------------------------------------------------------------------[ Relation ]
--{1

||| Build a model of the relations between domain and codomain.
export
mkRel : (Ord a, Ord b) => List (a,b) -> IMSet a b
mkRel = foldr (\(k,v),r => insert k (MSet.fromList [v]) r) empty

||| Apply a multiset to a relation, treating the relation like a function.
export
app : (Ord a, Ord b) => (f : IMSet a b) -> (xs : MSet a) -> MSet b
app f xs = foldr alg empty xs
  where alg : Cell a -> MSet b -> MSet b
        alg (Elem v n) r with (find v f)
          | Nothing = r
          | Just ys = union ys r

--}

-----------------------------------------------------------------------------------------[ Arrows ]
--{1

||| Type alias for mutiset to multiset mappings
public export
Arrow : Type -> Type -> Type
Arrow a b = (MSet a -> MSet b)

||| Build an Arrow for a given relation mapping.
export
mkArrow : (Ord a, Ord b) => List (a,b) -> Arrow a b
mkArrow = app . mkRel

||| Create a mutiset projection of an arrow given a multiset as input.
export
project : (Ord a, Ord b) => Arrow a b -> MSet a -> IMSet a b
project f xs = Foldable.foldr (\x,b => insert x (f $ MSet.fromList [x]) b) empty (elems xs)

--}

----------------------------------------------------------------------------------------[ Product ]
--{1

-- Take the cross product between two relations iff the elements share their domain element.
zipEq : (Ord a, Ord b, Ord c) => IMSet a b -> IMSet a c -> IMSet a (b,c)
zipEq xs ys = foldr alg empty xs
  where alg : Cell a b -> IMSet a (b,c) -> IMSet a (b,c)
        alg (Bin i x) bag with (IMSet.find i ys)
          | Nothing = bag
          | Just y  = let vs = MSet.fromList [(x',y') | x' <- elems x, y' <- elems y]
                      in insert i vs bag

infixr 9 :*:
||| Product between two arrows.
export
(:*:) : (Ord a, Ord b, Ord c, Ord (b,c))
     => Arrow a b -> Arrow a c -> MSet a -> MSet (b,c)
(:*:) f g xs = foldr alg empty bag
  where
    bag : IMSet a (b,c)
    bag = zipEq (project f xs) (project g xs)

    alg : Cell a (b,c) -> MSet (b,c) -> MSet (b,c)
    alg (Bin i x) set = union x set

--}

--------------------------------------------------------------------------------------[ Coproduct ]
--{1

infixr 8 :+:
||| Coroduct between two arrows.
export
(:+:) : (Ord a) => MSet a -> MSet a -> MSet a
(:+:) = union

--}


