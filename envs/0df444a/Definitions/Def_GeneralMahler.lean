-- Prove2me | Definitions.Def_GeneralMahler
-- name    : GeneralMahler
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:13.056354+00:00
-- url     : https://prove2.me/theorems/2df01f8f-096c-43cf-a17c-a082d9047b36
-- statement:
--   The file works in n-dimensional Euclidean space Rn(n) = ℝⁿ with its Euclidean inner product and Lebesgue volume. For a set K and a center z, polarAt(K,z) is the polar of K translated by z: the set of all vectors y such that ⟨y, x − z⟩ ≤ 1 for every x in K. The volumeProduct of K is defined as the infimum, over all centers z in the interior of K, of the product vol(K)·vol(polarAt(K,z)), where each volume is taken as a real number via the extended-real measure's toReal conversion. This is the Mahler volume product minimized over interior centers, rather than fixed at the origin or the Santaló point. The definitions themselves do not assume K is convex, bounded or measurable; for such sets, infinite volumes become zero under toReal, and an empty interior makes the infimum over the empty set equal to zero by the real sInf convention.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/GeneralMahler.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/GeneralMahler.lean; bytes 16..605
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

open Set MeasureTheory
open scoped RealInnerProductSpace

namespace GeneralMahler

abbrev Rn (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The polar of a convex body translated by an interior center. -/
def polarAt {n : ℕ} (K : Set (Rn n)) (z : Rn n) : Set (Rn n) :=
  {y | ∀ x ∈ K, ⟪y, x - z⟫ ≤ 1}

/-- The volume product minimized over the interior centers of the body. -/
def volumeProduct {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) : ℝ :=
  sInf ((fun z => (volume K).toReal * (volume (polarAt K z)).toReal) ''
    interior K)



end GeneralMahler
end
end OAI


