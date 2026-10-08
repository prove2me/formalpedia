-- Prove2me | Definitions.Def_InfiniteMatroid
-- name    : InfiniteMatroid
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:15.138482+00:00
-- url     : https://prove2.me/theorems/dc303e68-3e41-42a0-a2e6-f042cc9344b9
-- statement:
--   The block sets up notation for a matroid packing-and-covering problem on a ground set. D is the type of pairs consisting of a natural number m and a Boolean function on m-bit vectors (Fin m → Bool) → Bool, and E is the product ℤ × D, the ground-set type used for the counterexample setting. For a matroid M on α and a subset C, contractOnto(M,C) is the matroid on C obtained by taking the dual of M, restricting it to C, and dualizing back; this is the contraction of M onto C. HasPackingCovering(M₀,M₁) is a defined proposition, not an established theorem, saying that two matroids M₀ and M₁ on the same ground set have equal ground sets and that this set splits as a disjoint union of a packing part P and a covering part C, such that P contains disjoint sets S₀ and S₁ with S₀ spanning in the restriction M₀|P and S₁ spanning in the restriction M₁|P, while C contains sets I₀ and I₁, independent in contractOnto(M₀,C) and contractOnto(M₁,C) respectively, whose union is all of C.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/InfiniteMatroid.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/InfiniteMatroid.lean; bytes 16..690
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace InfiniteMatroidCounterexample
open Matroid

abbrev D := (m : ℕ) × ((Fin m → Bool) → Bool)
abbrev E := ℤ × D

def contractOnto {α : Type*} (M : Matroid α) (C : Set α) : Matroid α :=
  (M.dual ↾ C).dual

def HasPackingCovering {α : Type*} (M₀ M₁ : Matroid α) : Prop :=
  ∃ P C S₀ S₁ I₀ I₁ : Set α,
    Disjoint P C ∧ P ∪ C = M₀.E ∧ M₁.E = M₀.E ∧
    S₀ ⊆ P ∧ S₁ ⊆ P ∧ Disjoint S₀ S₁ ∧
    (M₀ ↾ P).Spanning S₀ ∧ (M₁ ↾ P).Spanning S₁ ∧
    I₀ ⊆ C ∧ I₁ ⊆ C ∧
    (contractOnto M₀ C).Indep I₀ ∧
    (contractOnto M₁ C).Indep I₁ ∧ I₀ ∪ I₁ = C



end InfiniteMatroidCounterexample
end OAI


