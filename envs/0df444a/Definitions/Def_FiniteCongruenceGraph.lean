-- Prove2me | Definitions.Def_FiniteCongruenceGraph
-- name    : FiniteCongruenceGraph
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:11.342957+00:00
-- url     : https://prove2.me/theorems/77f1ba0f-9c32-4587-9491-a54b1e8de973
-- statement:
--   An Algebra on a carrier type consists of a number of operations, an arity for each operation, and for each operation an interpretation as a map from arity-many carrier arguments to the carrier. A setoid (equivalence relation) on the carrier is Compatible with the algebra if, for every operation and every pair of argument tuples that are coordinatewise equivalent, the operation's outputs are equivalent. A Congruence is a compatible equivalence relation, and the congruences of an algebra are partially ordered by the order inherited from setoids. A lattice Lat is Representable if there is a positive size n and an algebra on Fin n whose congruence poset is order-isomorphic to Lat. For a Lat-valued coloring of carrier pairs, a placement map is Admissible if it never increases color: color(placement(l),placement(r)) ≤ color(l,r). A pair (l,r) is Marked relative to a finite set of seed pairs if some admissible placement sends some seed edge (a,b) to (l,r), and (l,r) are Connected if they are linked by a chain in the equivalence closure of Marked. IsGraphWitness for a coloring into a lattice with bottom requires five conditions: the color is symmetric; it equals ⊥ exactly on equal points; it satisfies the triangle inequality color(l,r) ≤ color(l,m) ⊔ color(m,r); whenever lower ≰ upper there is a pair with color ≤ lower but not ≤ upper; and for every nonempty finite seed set, any pair whose color is at most the supremum of the seed colors is Connected to each other via the seeds. HasGraphWitness(Lat) says there exist a positive size n and a coloring of Fin n pairs by Lat satisfying IsGraphWitness. These are defined propositions; no equivalence between Representable and HasGraphWitness is asserted in this block.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/FiniteCongruenceGraph.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/FiniteCongruenceGraph.lean; bytes 138..2595
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Setoid.Basic
import Mathlib.Order.Hom.Basic

namespace OAI

namespace FiniteCongruence

structure Algebra (Carrier : Type) where
  numOps : ℕ
  arity : Fin numOps → ℕ
  op : (index : Fin numOps) → (Fin (arity index) → Carrier) → Carrier

def Compatible {Carrier : Type} (alg : Algebra Carrier) (rel : Setoid Carrier) : Prop :=
  ∀ (index : Fin alg.numOps) (left right : Fin (alg.arity index) → Carrier),
    (∀ coord, rel (left coord) (right coord)) → rel (alg.op index left) (alg.op index right)

def Congruence {Carrier : Type} (alg : Algebra Carrier) :=
  {rel : Setoid Carrier // Compatible alg rel}

instance {Carrier : Type} (alg : Algebra Carrier) : PartialOrder (Congruence alg) :=
  inferInstanceAs (PartialOrder {rel : Setoid Carrier // Compatible alg rel})

def Representable (Lat : Type) [PartialOrder Lat] : Prop :=
  ∃ size : ℕ, 0 < size ∧ ∃ alg : Algebra (Fin size), Nonempty (Lat ≃o Congruence alg)

def Admissible {Lat Carrier : Type} [LE Lat] (color : Carrier → Carrier → Lat)
    (placement : Carrier → Carrier) : Prop :=
  ∀ left right, color (placement left) (placement right) ≤ color left right

def Marked {Lat Carrier : Type} [LE Lat] (color : Carrier → Carrier → Lat)
    (seeds : Finset (Carrier × Carrier)) (left right : Carrier) : Prop :=
  ∃ placement : Carrier → Carrier, Admissible color placement ∧
    ∃ edge ∈ seeds, placement edge.1 = left ∧ placement edge.2 = right

def Connected {Lat Carrier : Type} [LE Lat] (color : Carrier → Carrier → Lat)
    (seeds : Finset (Carrier × Carrier)) (left right : Carrier) : Prop :=
  Relation.EqvGen (Marked color seeds) left right

def IsGraphWitness {Lat Carrier : Type} [Lattice Lat] [OrderBot Lat]
    (color : Carrier → Carrier → Lat) : Prop :=
  (∀ left right, color left right = color right left) ∧
  (∀ left right, color left right = ⊥ ↔ left = right) ∧
  (∀ left right middle, color left right ≤ color left middle ⊔ color middle right) ∧
  (∀ lower upper : Lat, ¬ lower ≤ upper →
    ∃ left right, color left right ≤ lower ∧ ¬ color left right ≤ upper) ∧
  (∀ seeds : Finset (Carrier × Carrier), seeds.Nonempty → ∀ left right,
    color left right ≤ seeds.sup (fun edge => color edge.1 edge.2) →
      Connected color seeds left right)

def HasGraphWitness (Lat : Type) [Lattice Lat] [OrderBot Lat] : Prop :=
  ∃ size : ℕ, 0 < size ∧ ∃ color : Fin size → Fin size → Lat, IsGraphWitness color



end FiniteCongruence
end OAI


