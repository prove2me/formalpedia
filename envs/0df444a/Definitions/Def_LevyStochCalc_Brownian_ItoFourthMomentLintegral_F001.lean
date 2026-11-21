-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentLintegral_F001
-- name    : LevyStochCalc_Brownian_ItoFourthMomentLintegral_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:05:51.37136+00:00
-- url     : https://prove2.me/theorems/f3d6e680-db11-4768-995f-0af8729113c2
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoFourthMomentLintegral
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoFourthMomentLintegral. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentPartialSums_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentPartialSums_F003

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Fourth moment of the `L²` Itô integral

Truncation of a simple integrand and the `lintegral` form of the fourth-moment bound. Clamping
the coefficients to `[-C, C]` (`SimplePredictable.truncate`) moves a value no further from a
target already in `[-C, C]`, so a truncated approximant is still an approximant; the bound for
the simple integrands then passes to the `L²` Itô integral of any integrand bounded by `C` by
Fatou along an almost-everywhere convergent subsequence.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

section LintegralForm

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

/-- The fourth `lintegral` of an elementary integral as the `ofReal` of its fourth moment. -/
theorem SimplePredictable.lintegral_pow_four_eq {T : ℝ} (G : SimplePredictable Ω T)
    {C : ℝ} (hC : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ C) :
    ∫⁻ ω, (‖simpleIntegral W G T ω‖₊ : ℝ≥0∞) ^ 4 ∂P
      = ENNReal.ofReal (∫ ω, (simpleIntegral W G T ω) ^ 4 ∂P) := by
  have hmem : MemLp (fun ω => simpleIntegral W G T ω) 4 P := by
    have h := G.memLp_partialSum W hC 4 (by simp) G.N
    have hfun : G.partialSum W G.N = fun ω => simpleIntegral W G T ω := by
      funext ω; exact G.partialSum_card W ω
    rwa [hfun] at h
  have hmem' : MemLp (fun ω => simpleIntegral W G T ω) ((4 : ℕ) : ℝ≥0∞) P := by
    simpa using hmem
  have hint : Integrable (fun ω => (simpleIntegral W G T ω) ^ 4) P := by
    refine (hmem'.integrable_norm_pow (by norm_num)).mono
      ((continuous_pow 4).comp_aestronglyMeasurable hmem.1)
      (Filter.Eventually.of_forall fun ω => by simp)
  have hpt : ∀ ω, (‖simpleIntegral W G T ω‖₊ : ℝ≥0∞) ^ 4
      = ENNReal.ofReal ((simpleIntegral W G T ω) ^ 4) := by
    intro ω
    have h1 : (‖simpleIntegral W G T ω‖₊ : ℝ≥0∞)
        = ENNReal.ofReal |simpleIntegral W G T ω| := by
      rw [ENNReal.ofReal_eq_coe_nnreal (abs_nonneg _)]
      exact congrArg _ (NNReal.eq (by simp [Real.norm_eq_abs]))
    rw [h1, ← ENNReal.ofReal_pow (abs_nonneg _), ← abs_pow,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ simpleIntegral W G T ω ^ 4)]
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun ω => by positivity)]
  exact lintegral_congr hpt
include hℱ in
/-- The fourth-moment bound for a simple integrand, in `lintegral` form. -/
theorem SimplePredictable.lintegral_simpleIntegral_pow_four_le {T : ℝ}
    (G : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (G.partition i.castSucc)) (G.ξ i))
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ C) :
    ∫⁻ ω, (‖simpleIntegral W G T ω‖₊ : ℝ≥0∞) ^ 4 ∂P
      ≤ ENNReal.ofReal ((6 + gaussianFourthMoment) * C ^ 4 * T ^ 2) := by
  rw [G.lintegral_pow_four_eq W hC]
  exact ENNReal.ofReal_le_ofReal
    (G.integral_simpleIntegral_pow_four_le_horizon W ℱ hℱ h_adapt hC0 hC)
include hℱ in
/-- The fourth-moment bound against a per-tile coefficient bound, in `lintegral` form. -/
theorem SimplePredictable.lintegral_simpleIntegral_pow_four_le_varClock {T : ℝ}
    (G : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (G.partition i.castSucc)) (G.ξ i))
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ C)
    {c : Fin G.N → ℝ} (hc : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ c i) :
    ∫⁻ ω, (‖simpleIntegral W G T ω‖₊ : ℝ≥0∞) ^ 4 ∂P
      ≤ ENNReal.ofReal ((6 + gaussianFourthMoment) * G.varClock c G.N ^ 2) := by
  rw [G.lintegral_pow_four_eq W hC]
  exact ENNReal.ofReal_le_ofReal
    (G.integral_simpleIntegral_pow_four_le_varClock W ℱ hℱ h_adapt hC0 hC hc)
end LintegralForm

end LevyStochCalc.Brownian.Ito


