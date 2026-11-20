-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedIsometryL2_F001
-- name    : LevyStochCalc_Poisson_CompensatedIsometryL2_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T16:44:04.594772+00:00
-- url     : https://prove2.me/theorems/fb1ba392-0d44-4d35-b5c6-15bd28776258
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedIsometryL2
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedIsometryL2. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Batteries.Tactic.OpenPrivate
import Definitions.Def_LevyStochCalc_Poisson_CompensatedIsometryL2_F000
import Definitions.Def_SourceProof_585438f7fe1537e8a461ed92
import Definitions.Def_SourceProof_787d81ef0709384e49c1ae7f

open private simpleIntegral_sq_bochner_eq from Definitions.Def_LevyStochCalc_Poisson_CompensatedIsometryL2_F000
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# L²-isometry of the simple compensated-Poisson integral

Expansion of `(∑_i ξ_i · Ñ(B_i))²` into its diagonal and off-diagonal terms, the resulting
isometry `∫⁻ ‖simpleIntegral N φ T‖² ∂P = ∫⁻ ∫⁻ ∫⁻ ‖φ.eval‖² ∂ν ∂volume ∂P` together with
its Bochner sum form `∑_i ν̂(fullRect i).toReal · ∫ ξ_i² ∂P`, the finiteness of the
`L²`-norm and the membership `MemLp (simpleIntegral N φ T) 2 P`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

lemma simpleIntegral_isometry
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {T : ℝ} (hT : 0 < T) (φ : SimplePredictable Ω E ν T)
    (h_adapt : ∀ i : Fin φ.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (φ.partition i.castSucc)) (φ.ξ i)) :
    ∫⁻ ω, (‖simpleIntegral N φ T ω‖₊ : ℝ≥0∞) ^ 2 ∂P =
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by
  rw [_root_.Prove2MeSourceProof.h_787d81ef0709384e49c1ae7f N ℱ hℱ hT φ h_adapt]
  rw [_root_.Prove2MeSourceProof.h_585438f7fe1537e8a461ed92 φ]
/-- **B3 sum form: L² isometry (Bochner) for the compensated-Poisson simple
integral.** For an adapted simple `φ`,
`E[(simpleIntegral N φ T)²] = Σ_i ν̂(fullRect i).toReal · E[ξ_i²]`.

Combines `simpleIntegral_eq_sum_fullRect` (sum decomposition of the
integral at time `T`) with the existing private `simpleIntegral_sq_bochner_eq`. -/
theorem simpleIntegral_L2_isometry_compensatedPoisson_sumForm
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {T : ℝ} (φ : SimplePredictable Ω E ν T)
    (h_adapt : ∀ i : Fin φ.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (φ.partition i.castSucc)) (φ.ξ i)) :
    ∫ ω, (simpleIntegral N φ T ω) ^ 2 ∂P
      = ∑ i : Fin φ.N,
        (LevyStochCalc.Poisson.referenceIntensity ν (φ.fullRect i)).toReal *
        ∫ ω, (φ.ξ i ω) ^ 2 ∂P := by
  have h_eq : ∀ ω, (simpleIntegral N φ T ω) ^ 2
      = (∑ i : Fin φ.N, φ.ξ i ω * N.compensated (φ.fullRect i) ω) ^ 2 := by
    intro ω; rw [simpleIntegral_eq_sum_fullRect]
  simp_rw [h_eq]
  exact simpleIntegral_sq_bochner_eq N ℱ hℱ φ h_adapt
/-! ## Square integrability of the simple compensated integral

The simple integral `simpleIntegral N φ T` of an adapted simple integrand has finite second
moment and lies in `L²(P)`; the Brownian counterpart is the lift
`LevyStochCalc.Brownian.Ito.simpleIntegralLp_brownian` to `Lp ℝ 2 P`. -/

/-- **Finite L²-norm of `simpleIntegral N φ T`.** Combines `simpleIntegral_isometry`
(which gives `∫⁻ ‖simpleIntegral‖² = ∑_i ν̂(rect_i) · ∫⁻ ξ_i²`) with the
boundedness of `ξ_i` and finiteness of `ν̂(rect_i) = (t_{i+1} - t_i) · ν(A_i)`. -/
lemma simpleIntegral_lintegral_sq_finite_compensated
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {T : ℝ} (hT : 0 < T) (φ : SimplePredictable Ω E ν T)
    (h_adapt : ∀ i : Fin φ.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (φ.partition i.castSucc)) (φ.ξ i)) :
    ∫⁻ ω, (‖simpleIntegral N φ T ω‖₊ : ℝ≥0∞) ^ 2 ∂P < ⊤ := by
  rw [simpleIntegral_isometry N ℱ hℱ hT φ h_adapt]
  rw [_root_.Prove2MeSourceProof.h_585438f7fe1537e8a461ed92 φ]
  -- Goal: ∑ i, ν̂(fullRect i) * ∫⁻ ‖ξ i‖₊² ∂P < ⊤
  refine ENNReal.sum_lt_top.mpr (fun i _ => ?_)
  refine ENNReal.mul_lt_top ?_ ?_
  · -- ν̂(fullRect i) < ⊤. fullRect i = (partition i.castSucc, partition i.succ] × A_i.
    -- referenceIntensity = vol.restrict [0, ∞) ⊗ ν.
    -- ν̂(rect) = (length of time interval) · ν(A_i). Both finite.
    unfold LevyStochCalc.Poisson.referenceIntensity SimplePredictable.fullRect
    rw [MeasureTheory.Measure.prod_prod]
    refine ENNReal.mul_lt_top ?_ ?_
    · -- vol.restrict [0,∞) (Ioc s t) ≤ vol (Ioc s t) = ENNReal.ofReal (t - s) < ⊤.
      refine lt_of_le_of_lt
        (MeasureTheory.Measure.restrict_apply_le (Set.Ici (0 : ℝ)) _) ?_
      rw [Real.volume_Ioc]
      exact ENNReal.ofReal_lt_top
    · exact lt_of_le_of_ne le_top (φ.A_finite i)
  · -- ∫⁻ ω, ‖ξ i ω‖₊² ∂P < ⊤. ξ_i bounded ⟹ integrand bounded ⟹ finite
    --   on probability.
    obtain ⟨M, hM⟩ := φ.ξ_bounded i
    have h_bound : ∀ ω, |φ.ξ i ω| ≤ max M 0 :=
      fun ω => le_trans (hM ω) (le_max_left _ _)
    have h_M_nn : 0 ≤ max M 0 := le_max_right _ _
    have h_norm_le : ∀ ω, (‖φ.ξ i ω‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal (max M 0) := by
      intro ω
      rw [show (‖φ.ξ i ω‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖φ.ξ i ω‖
            from (ofReal_norm _).symm]
      exact ENNReal.ofReal_le_ofReal (Real.norm_eq_abs _ ▸ h_bound ω)
    calc ∫⁻ ω, (‖φ.ξ i ω‖₊ : ℝ≥0∞) ^ 2 ∂P
        ≤ ∫⁻ _ω, (ENNReal.ofReal (max M 0)) ^ 2 ∂P := by
          refine MeasureTheory.lintegral_mono (fun ω => ?_)
          exact pow_le_pow_left' (h_norm_le ω) 2
      _ = (ENNReal.ofReal (max M 0)) ^ 2 * P Set.univ := by
          rw [MeasureTheory.lintegral_const]
      _ < ⊤ := by
          rw [MeasureTheory.measure_univ, mul_one]
          exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top
end LevyStochCalc.Poisson.Compensated


