-- Prove2me | Definitions.Def_SourceProof_787d81ef0709384e49c1ae7f
-- name    : SourceProof_787d81ef0709384e49c1ae7f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T16:41:09.757411+00:00
-- url     : https://prove2.me/theorems/99851216-3c3e-4c96-8874-f70dc8df4691
-- title:
--   LevyStochCalc source module: SourceProof_787d81ef0709384e49c1ae7f
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.simpleIntegral_sq_lintegral_eq` comes from the `LevyStochCalc.Poisson.CompensatedIsometryL2` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Batteries.Tactic.OpenPrivate
import Definitions.Def_LevyStochCalc_Poisson_CompensatedIsometryL2_F000

open private cross_sq_integrable simpleIntegral_sq_bochner_eq from Definitions.Def_LevyStochCalc_Poisson_CompensatedIsometryL2_F000
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

set_option maxHeartbeats 800000 in
-- maxHeartbeats: typechecker budget for proof-heavy goal below.

theorem _root_.Prove2MeSourceProof.h_787d81ef0709384e49c1ae7f
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {T : ℝ} (_hT : 0 < T) (φ : SimplePredictable Ω E ν T)
    (h_adapt : ∀ i : Fin φ.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (φ.partition i.castSucc)) (φ.ξ i)) :
    ∫⁻ ω, (‖simpleIntegral N φ T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∑ i : Fin φ.N,
        LevyStochCalc.Poisson.referenceIntensity ν (φ.fullRect i) *
        ∫⁻ ω, (‖φ.ξ i ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
  -- Step 1: rewrite simpleIntegral as sum over fullRect.
  simp_rw [LevyStochCalc.Poisson.Compensated.simpleIntegral_eq_sum_fullRect N φ]
  -- Step 2: convert (‖x‖)² to ENNReal.ofReal(x²).
  have h_norm_sq_eq : ∀ x : ℝ, (‖x‖₊ : ℝ≥0∞)^2 = ENNReal.ofReal (x^2) := fun x => by
    rw [show (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ from ofReal_norm x |>.symm]
    rw [← ENNReal.ofReal_pow (norm_nonneg _)]
    rw [show ‖x‖^2 = x^2 from by rw [Real.norm_eq_abs, sq_abs]]
  rw [show (∫⁻ ω,
        (‖∑ i, φ.ξ i ω * N.compensated (φ.fullRect i) ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
        = ∫⁻ ω, ENNReal.ofReal
            ((∑ i, φ.ξ i ω * N.compensated (φ.fullRect i) ω)^2) ∂P from
    MeasureTheory.lintegral_congr (fun ω => h_norm_sq_eq _)]
  -- Step 3: integrability and nonnegativity for ofReal_integral_eq_lintegral_ofReal.
  have h_int_sum_sq : MeasureTheory.Integrable
      (fun ω => (∑ i, φ.ξ i ω * N.compensated (φ.fullRect i) ω)^2) P := by
    -- (∑ a)² = ∑∑ a_i a_j; sum of integrables.
    have h_eq : ∀ ω, (∑ i : Fin φ.N, φ.ξ i ω * N.compensated (φ.fullRect i) ω)^2
                = ∑ i : Fin φ.N, ∑ j : Fin φ.N,
                  (φ.ξ i ω * N.compensated (φ.fullRect i) ω) *
                  (φ.ξ j ω * N.compensated (φ.fullRect j) ω) := by
      intro ω; rw [sq]; exact Finset.sum_mul_sum _ _ _ _
    rw [show (fun ω => (∑ i, φ.ξ i ω * N.compensated (φ.fullRect i) ω)^2)
          = fun ω => ∑ i : Fin φ.N, ∑ j : Fin φ.N,
              (φ.ξ i ω * N.compensated (φ.fullRect i) ω) *
              (φ.ξ j ω * N.compensated (φ.fullRect j) ω) from funext h_eq]
    refine MeasureTheory.integrable_finsetSum _ (fun i _ => ?_)
    refine MeasureTheory.integrable_finsetSum _ (fun j _ => ?_)
    exact cross_sq_integrable N φ i j
  have h_nn_sum_sq :
      0 ≤ᵐ[P] fun ω => (∑ i, φ.ξ i ω * N.compensated (φ.fullRect i) ω)^2 := by
    filter_upwards with ω; exact sq_nonneg _
  -- Step 4: apply ofReal_integral_eq_lintegral_ofReal
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int_sum_sq h_nn_sum_sq]
  -- Step 5: apply Bochner LHS reduction.
  rw [simpleIntegral_sq_bochner_eq N ℱ hℱ φ h_adapt]
  -- Step 6: convert ENNReal.ofReal of finite sum to finite sum of ENNReal terms.
  rw [show
        ENNReal.ofReal (∑ i : Fin φ.N,
          (LevyStochCalc.Poisson.referenceIntensity ν (φ.fullRect i)).toReal *
          ∫ ω, (φ.ξ i ω)^2 ∂P)
        = ∑ i : Fin φ.N,
          ENNReal.ofReal
            ((LevyStochCalc.Poisson.referenceIntensity ν (φ.fullRect i)).toReal *
            ∫ ω, (φ.ξ i ω)^2 ∂P) from by
    rw [ENNReal.ofReal_sum_of_nonneg]
    intro i _
    refine mul_nonneg ENNReal.toReal_nonneg ?_
    exact MeasureTheory.integral_nonneg (fun ω => sq_nonneg _)]
  -- Step 7: each term: ofReal(ν̂.toReal · ∫ ξ²) = ν̂ · ofReal(∫ ξ²)
  --   = ν̂ · ∫⁻ ‖ξ‖².
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h_finite_i : LevyStochCalc.Poisson.referenceIntensity ν (φ.fullRect i) ≠ ⊤ := by
    rw [(_root_.Prove2MeSourceProof.h_c270d540a1c5354737ac7c4b φ) i]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (φ.A_finite i)
  -- Bound ξ_i² by M_i² to get integrability.
  obtain ⟨M, hM⟩ := φ.ξ_bounded i
  have h_xi_sq_bound : ∀ ω : Ω, (φ.ξ i ω)^2 ≤ M^2 := fun ω =>
    sq_le_sq' (neg_le_of_abs_le (hM ω)) (le_of_abs_le (hM ω))
  have h_int_xi_sq : MeasureTheory.Integrable (fun ω => (φ.ξ i ω)^2) P := by
    refine MeasureTheory.Integrable.mono' (g := fun _ : Ω => M^2)
      (MeasureTheory.integrable_const _) ?_ ?_
    · exact ((φ.ξ_measurable i).pow_const 2).aestronglyMeasurable
    · filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact h_xi_sq_bound ω
  have h_nn_xi_sq : 0 ≤ᵐ[P] fun ω => (φ.ξ i ω)^2 := by
    filter_upwards with ω; positivity
  -- ofReal(ν̂.toReal · ∫ ξ²) = ofReal(ν̂.toReal) · ofReal(∫ ξ²)
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg]
  -- ofReal(ν̂.toReal) = ν̂
  rw [ENNReal.ofReal_toReal h_finite_i]
  -- ofReal(∫ ξ²) = ∫⁻ ENNReal.ofReal(ξ²)
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int_xi_sq h_nn_xi_sq]
  -- ∫⁻ ENNReal.ofReal(ξ²) = ∫⁻ (‖ξ‖)² (by h_norm_sq_eq backwards)
  rw [show (fun ω => ENNReal.ofReal ((φ.ξ i ω)^2))
        = fun ω => (‖φ.ξ i ω‖₊ : ℝ≥0∞) ^ 2 from
    funext (fun ω => (h_norm_sq_eq _).symm)]
/-! ## Square integrability of the simple compensated integral

The simple integral `simpleIntegral N φ T` of an adapted simple integrand has finite second
moment and lies in `L²(P)`; the Brownian counterpart is the lift
`LevyStochCalc.Brownian.Ito.simpleIntegralLp_brownian` to `Lp ℝ 2 P`. -/

end LevyStochCalc.Poisson.Compensated


