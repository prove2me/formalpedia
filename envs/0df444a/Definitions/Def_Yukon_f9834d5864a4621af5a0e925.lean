-- Prove2me | Definitions.Def_Yukon_f9834d5864a4621af5a0e925
-- name    : Yukon_f9834d5864a4621af5a0e925
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T07:39:40.468724+00:00
-- url     : https://prove2.me/theorems/5d9779c4-99a8-4da0-b9b9-098b9e90dba5
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.BoundaryTailCoordinate.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.BoundaryTailCoordinate.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/BoundaryTailCoordinate.lean
--
--   yukon-proof-operation:foundation-direct-6f51821224f6ae6c969c19e8e66aba77ae5831a9785a284cb07aae839e292001
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiNDIxMjZkYzAxM2NjNTgyNzUzMzllYTdiNWUwNjI1ODM1YjczZDRkZGVmNTM0MzNjYWM4MGIxMTk4OWE1NDVlMSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTZmNTE4MjEyMjRmNmFlNmM5NjljMTllOGU2NmFiYTc3YWU1ODMxYTk3ODVhMjg0Y2IwN2FhZTgzOWUyOTIwMDEiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl9mOTgzNGQ1ODY0YTQ2MjFhZjVhMGU5MjUiLCJ2IjoyfQ]

import Definitions.Def_Yukon_043883ce6ed32260483e0ffb

import Definitions.Def_Yukon_273df68c1ff8e6ab04d115a8












































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.BoundaryTailAlgebra

open RCN002 RCN055 RCN057 RCN064 RCN086 RCN095 RCN114 RCN136 RCN156
open RCN187 RCN199 RCN204 RCN234 RCN257 RCN271 RCN295 RCN313 RCN341 RCN344

noncomputable section
variable {K Ω : Type} [Field K] [Field Ω]

theorem coordinate_eval₂ (P : Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]
    (Q : MvPolynomial (Fin 3) Ω) :
    MvPolynomial.eval₂Hom (algebraMap Ω (CoordinateField Ω P)) (coordinate Ω P) Q =
      coordinateEvaluation Ω P Q := by
  rw [coordinateEvaluation_eq_aeval]
  exact (MvPolynomial.aeval_eq_eval₂Hom _ _).symm

theorem coordinate_global_tail_pole_le
    (P : Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]
    (V : Place Ω (CoordinateField Ω P))
    (φ : Polynomial K →+* Ω) (hφ : Function.Injective φ)
    (F : MvPolynomial (Fin 4) K) (m₀ m r v z p : ℕ) [CharP K p]
    (hm₀ : 1 ≤ m₀) (hm : 1 ≤ m) (hchar : 2 * m₀ < p)
    (hr : 3 ≤ r) (hv : 2 ≤ v)
    (hR : WeightBound residualSWeights F (r : ℤ))
    (hYR : WeightBound residualYSWeights F ((r + v : ℕ) : ℤ))
    (hAll : WeightBound residualTotalWeights F ((r + v + z : ℕ) : ℤ))
    (hH : surfaceMap φ (polyH K F) ∉ P)
    (hfirst : globalTailCut φ F (m₀ + 2) ∈ P) :
    2 * poleOrder V.val (coordinateEvaluation Ω P (globalTailCut φ F (m + 2)) /
      coordinateEvaluation Ω P (surfaceMap φ (polyH K F)) ^ (m + 1)) ≤
      2 * flagPole V.val (coordinate Ω P) (normalFlag m r v z) +
        ((m : ℤ) + 2) * movingPoleTarget P
          (surfaceMap φ (polyH K F)) (surfaceMap φ (polyG K F)) V := by
  have hHne : coordinateEvaluation Ω P (surfaceMap φ (polyH K F)) ≠ 0 := by
    intro hz
    apply hH
    rw [← coordinateEvaluation_ker Ω P]
    exact hz
  have hfirstzero : coordinateEvaluation Ω P (globalTailCut φ F (m₀ + 2)) = 0 := by
    change globalTailCut φ F (m₀ + 2) ∈ RingHom.ker (coordinateEvaluation Ω P).toRingHom
    rw [coordinateEvaluation_ker]
    exact hfirst
  have hcoeff : ∀ a : Ω, a ≠ 0 → V.val (algebraMap Ω (CoordinateField Ω P) a) = 1 := by
    letI : V.val.IsTrivialOn Ω := V.property.2
    exact Valuation.IsTrivialOn.eq_one
  have h := global_tail_normalized_pole_le V.val (algebraMap Ω (CoordinateField Ω P))
    hcoeff (coordinate Ω P) φ hφ F m₀ m r v z p hm₀ hm hchar hr hv hR hYR hAll
    (by rwa [coordinate_eval₂]) (by rwa [coordinate_eval₂])
  simpa only [coordinate_eval₂, movingPoleTarget, movingRatio, flagPole_unitAll,
    flagPole_unitYZ] using h

theorem global_tail_zero_count [IsAlgClosed Ω]
    (P : Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]
    (φ : Polynomial K →+* Ω) (hφ : Function.Injective φ)
    (F : MvPolynomial (Fin 4) K) (m₀ m r v z p factor : ℕ) [CharP K p]
    (hm₀ : 1 ≤ m₀) (hm : 1 ≤ m) (hchar : 2 * m₀ < p)
    (hr : 3 ≤ r) (hv : 2 ≤ v) (hfactor : m + 2 ≤ 2 * factor)
    (hR : WeightBound residualSWeights F (r : ℤ))
    (hYR : WeightBound residualYSWeights F ((r + v : ℕ) : ℤ))
    (hAll : WeightBound residualTotalWeights F ((r + v + z : ℕ) : ℤ))
    (budget : MovingPoleBudget P (surfaceMap φ (polyH K F)) (surfaceMap φ (polyG K F)))
    (base : SeparableLiteralCoordinate P)
    (hH : surfaceMap φ (polyH K F) ∉ P)
    (hfirst : globalTailCut φ F (m₀ + 2) ∈ P)
    (hlater : globalTailCut φ F (m + 2) ∉ P) :
    FiniteRegularZeroSetBound P (surfaceMap φ (polyH K F)) (globalTailCut φ F (m + 2))
      (budget.weightedCost (normalFlag m r v z) + factor * budget.movingCost) := by
  apply budget.zero_le_of_doubled_pole base _ (m + 1) factor _ hH hlater
  intro V
  apply (coordinate_global_tail_pole_le P V φ hφ F m₀ m r v z p hm₀ hm hchar
    hr hv hR hYR hAll hH hfirst).trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_right (by exact_mod_cast hfactor)
  simp only [movingPoleTarget, poleOrder]
  positivity

end
end ProximityPrize.SubmissionLower.BoundaryTailAlgebra


