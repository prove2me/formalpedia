-- Prove2me | Definitions.Def_Yukon_273df68c1ff8e6ab04d115a8
-- name    : Yukon_273df68c1ff8e6ab04d115a8
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T07:25:58.226757+00:00
-- url     : https://prove2.me/theorems/f4e51e01-61b9-47dc-9946-3da82cbdf6ac
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.BoundaryTailZeroCount.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.BoundaryTailZeroCount.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/BoundaryTailZeroCount.lean
--
--   yukon-proof-operation:foundation-direct-763fe3a1ab4067f4784296e70b3c2d825669afcbe40d836a1bf2e63e03832258
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiODJhMjU4NmRkMDFlNjJmNmQyOWYwNDYxYTE5NzdiZjc5YmM3MWM2ZjQ0YTViZGNjMjFlZDBlNGNjZTE0MDU3NyIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTc2M2ZlM2ExYWI0MDY3ZjQ3ODQyOTZlNzBiM2MyZDgyNTY2OWFmY2JlNDBkODM2YTFiZjJlNjNlMDM4MzIyNTgiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl8yNzNkZjY4YzFmZjhlNmFiMDRkMTE1YTgiLCJ2IjoyfQ]

import Definitions.Def_Yukon_043883ce6ed32260483e0ffb













































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.RCN199
open scoped Classical BigOperators WithZero
open RCN002 RCN344 RCN341 RCN095 RCN114 RCN295 RCN187 RCN207 RCN064 RCN204 RCN271 RCN257
noncomputable section
set_option autoImplicit false
variable {K : Type} [Field K]
variable {P : Ideal (MvPolynomial (Fin 3) K)} [P.IsPrime]
variable {H G : MvPolynomial (Fin 3) K}

namespace MovingPoleBudget

theorem zero_le_of_doubled_pole [IsAlgClosed K]
    (budget : MovingPoleBudget P H G)
    (base : SeparableLiteralCoordinate P)
    (T : MvPolynomial (Fin 3) K) (denom factor : ℕ) (q : FlagDegree)
    (hH : H ∉ P) (hT : T ∉ P)
    (hpole : ∀ v : Place K (CoordinateField K P),
      2 * poleOrder v.val
          (coordinateEvaluation K P T /
            (coordinateEvaluation K P H)^denom) ≤
        2 * flagPole v.val (coordinate K P) q +
          (2 * factor : ℕ) * movingPoleTarget P H G v) :
    FiniteRegularZeroSetBound P H T
      (budget.weightedCost q + factor * budget.movingCost) := by
  apply finite_regular_zero_bound_of_separator K P base H T denom _ hT hH
  intro W
  have hlocal : ∀ v ∈ W,
      (2 * poleOrder v.val
          (coordinateEvaluation K P T /
            (coordinateEvaluation K P H)^denom) : ℤ) ≤
        2 * flagPole v.val (coordinate K P) q +
          (2 * factor : ℤ) * movingPoleTarget P H G v := by
    intro v hv
    exact hpole v
  have hsum := Finset.sum_le_sum hlocal
  have hflag := budget.sum_flagPole_le q W
  have hmove := budget.movingPole W
  have hbound :
      (2 : ℤ) * (∑ v ∈ W, poleOrder v.val
        (coordinateEvaluation K P T /
          (coordinateEvaluation K P H)^denom)) ≤
      (2 : ℤ) * (budget.weightedCost q + factor * budget.movingCost) := by
    calc
      _ = ∑ v ∈ W, (2 * poleOrder v.val
          (coordinateEvaluation K P T /
            (coordinateEvaluation K P H)^denom) : ℤ) := by
            simp only [Finset.mul_sum]
      _ ≤ ∑ v ∈ W, (2 * flagPole v.val (coordinate K P) q +
          (2 * factor : ℤ) * movingPoleTarget P H G v) := hsum
      _ = (2 : ℤ) * ((∑ v ∈ W, flagPole v.val (coordinate K P) q) +
          (factor : ℤ) * ∑ v ∈ W, movingPoleTarget P H G v) := by
            simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
            push_cast
            ring
      _ ≤ (2 : ℤ) * (budget.weightedCost q + factor * budget.movingCost) := by
            gcongr
  have hfinal :
      (∑ v ∈ W, poleOrder v.val
        (coordinateEvaluation K P T /
          (coordinateEvaluation K P H)^denom) : ℤ) ≤
        (budget.weightedCost q + factor * budget.movingCost : ℤ) := by
    linarith
  simpa only [RCN346.poleOrder, coordinateEvaluation_eq_aeval,
    Nat.cast_add, Nat.cast_mul] using hfinal

end MovingPoleBudget
end
end ProximityPrize.SubmissionLower.RCN199


