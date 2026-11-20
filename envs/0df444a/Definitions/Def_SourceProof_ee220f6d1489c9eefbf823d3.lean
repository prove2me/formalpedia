-- Prove2me | Definitions.Def_SourceProof_ee220f6d1489c9eefbf823d3
-- name    : SourceProof_ee220f6d1489c9eefbf823d3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T19:10:59.534178+00:00
-- url     : https://prove2.me/theorems/b57498b7-e9f6-42bc-a02b-e25e2123d93a
-- title:
--   LevyStochCalc source module: SourceProof_ee220f6d1489c9eefbf823d3
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.simpleIntegral_memLp_compensated` comes from the `LevyStochCalc.Poisson.CompensatedIsometryL2` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedIsometryL2_F001

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

/-! ## Square integrability of the simple compensated integral

The simple integral `simpleIntegral N φ T` of an adapted simple integrand has finite second
moment and lies in `L²(P)`; the Brownian counterpart is the lift
`LevyStochCalc.Brownian.Ito.simpleIntegralLp_brownian` to `Lp ℝ 2 P`. -/


theorem _root_.Prove2MeSourceProof.h_ee220f6d1489c9eefbf823d3
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {T : ℝ} (hT : 0 < T) (φ : SimplePredictable Ω E ν T)
    (h_adapt : ∀ i : Fin φ.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (φ.partition i.castSucc)) (φ.ξ i)) :
    MeasureTheory.MemLp (fun ω => simpleIntegral N φ T ω) 2 P := by
  refine ⟨?_, ?_⟩
  · -- AEStronglyMeasurable.
    refine Measurable.aestronglyMeasurable ?_
    unfold LevyStochCalc.Poisson.Compensated.simpleIntegral
    refine Finset.measurable_sum _ (fun i _ => ?_)
    refine Measurable.mul (φ.ξ_measurable i) ?_
    -- N.compensated B = (N.N · B).toReal - ν̂(B).toReal. Measurable in ω.
    unfold LevyStochCalc.Poisson.PoissonRandomMeasure.compensated
    refine Measurable.sub ?_ measurable_const
    have h_meas_NB : Measurable (fun ω => N.N ω (φ.timeRect i T)) := by
      apply N.measurable_eval
      -- timeRect i T is measurable (Ioc × A_i with A_i measurable).
      unfold LevyStochCalc.Poisson.Compensated.SimplePredictable.timeRect
      exact MeasurableSet.prod measurableSet_Ioc (φ.A_measurable i)
    exact ENNReal.measurable_toReal.comp h_meas_NB
  · -- eLpNorm < ⊤.
    rw [MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
        (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by simp : (2 : ℝ≥0∞) ≠ ⊤)]
    have h_two_toReal : (2 : ℝ≥0∞).toReal = 2 := by simp
    rw [h_two_toReal]
    have h_pre := LevyStochCalc.Poisson.Compensated.simpleIntegral_lintegral_sq_finite_compensated N ℱ hℱ hT φ h_adapt
    have h_rewrite : ∀ ω : Ω,
        (‖LevyStochCalc.Poisson.Compensated.simpleIntegral N φ T ω‖ₑ : ℝ≥0∞) ^ (2 : ℝ)
          = (‖LevyStochCalc.Poisson.Compensated.simpleIntegral N φ T ω‖₊ : ℝ≥0∞) ^ 2 := by
      intro ω
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
      rfl
    rw [show (fun ω => (‖LevyStochCalc.Poisson.Compensated.simpleIntegral N φ T ω‖ₑ : ℝ≥0∞) ^ (2 : ℝ))
          = (fun ω => (‖LevyStochCalc.Poisson.Compensated.simpleIntegral N φ T ω‖₊ : ℝ≥0∞) ^ 2) from
        funext h_rewrite]
    exact h_pre
end LevyStochCalc.Poisson.Compensated


