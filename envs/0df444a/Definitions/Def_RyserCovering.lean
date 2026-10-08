-- Prove2me | Definitions.Def_RyserCovering
-- name    : RyserCovering
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:17.405502+00:00
-- url     : https://prove2.me/theorems/070b80b7-138b-4efb-94e4-f2807876a5f6
-- statement:
--   A hypergraph on a vertex type V is a finite set of finite subsets (edges) of V. A set C of vertices is a cover if every edge contains some vertex of C, and a hypergraph is intersecting if any two distinct edges have nonempty intersection. The matchings of a hypergraph are its subfamilies of pairwise disjoint edges, the matching number is the largest cardinality of such a subfamily, and the cover number is the least cardinality of a cover, taken as the infimum of the set of achievable cover sizes (which is 0 in Lean's convention if no cover exists). Given a map part from vertices to an index type I, a hypergraph is part-uniform if every edge contains exactly one vertex from each class part⁻¹(i), and it is r-partite uniform if some map part : V → Fin r has this property. CounterexampleRank(r) is a defined proposition, not an established theorem: it asserts that there exist a finite type V with decidable equality and a hypergraph H on V such that r > 0, H is nonempty, H is r-partite uniform, H is intersecting, some cover of H exists, the matching number of H equals 1, and the cover number of H equals r.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/RyserCovering.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/RyserCovering.lean; bytes 16..1485
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample

abbrev Hypergraph (V : Type*) := Finset (Finset V)

section

variable {V : Type*} [DecidableEq V]

def IsCover (H : Hypergraph V) (C : Finset V) : Prop :=
  ∀ e ∈ H, ∃ v ∈ C, v ∈ e

def Intersecting (H : Hypergraph V) : Prop :=
  ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).Nonempty

attribute [-instance] instDecidablePairwiseCoeFinsetOfDecidableEqOfDecidableRel in
def matchings (H : Hypergraph V) : Finset (Hypergraph V) := by
  classical
  exact H.powerset.filter fun M => (M : Set (Finset V)).Pairwise Disjoint

def matchingNumber (H : Hypergraph V) : ℕ := (matchings H).sup Finset.card

def coverCardinalities (H : Hypergraph V) : Set ℕ :=
  {n | ∃ C : Finset V, IsCover H C ∧ C.card = n}

def coverNumber (H : Hypergraph V) : ℕ := sInf (coverCardinalities H)

def PartiteUniform {I : Type*} (part : V → I) (H : Hypergraph V) : Prop :=
  ∀ e ∈ H, ∀ i : I, ∃! v : V, v ∈ e ∧ part v = i

def RPartiteUniform (r : ℕ) (H : Hypergraph V) : Prop :=
  ∃ part : V → Fin r, PartiteUniform part H

end

def CounterexampleRank (r : ℕ) : Prop :=
  ∃ (V : Type) (fin : Fintype V) (dec : DecidableEq V),
    letI : Fintype V := fin
    letI : DecidableEq V := dec
    ∃ H : Hypergraph V,
      0 < r ∧ H.Nonempty ∧ RPartiteUniform r H ∧ Intersecting H ∧
        (∃ C : Finset V, IsCover H C) ∧ matchingNumber H = 1 ∧ coverNumber H = r



end RyserCoveringCounterexample
end
end OAI


