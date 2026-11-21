-- Prove2me | Definitions.Def_LevyStochCalc_Ito_PicardIntegrandBounds_F003
-- name    : LevyStochCalc_Ito_PicardIntegrandBounds_F003
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:16:08.003533+00:00
-- url     : https://prove2.me/theorems/f0396dd0-e1c0-4f56-8899-ce0525b75ee0
-- title:
--   Source declarations: LevyStochCalc.Ito.PicardIntegrandBounds
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.PicardIntegrandBounds. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardIntegrandBounds_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Square integrability of the Picard integrands along a state process

Linear growth of the coefficients, read off the Lipschitz hypothesis by comparison with the
state `0`, turns the bounds at that single state recorded by `IsRegular` into bounds along a
state process: whenever the state has finite energy over every horizon, the drift, diffusion
and jump integrands evaluated along it are square integrable at every horizon, and a member of
the process space frozen at `T` has that energy. Composing a jointly measurable coefficient
with a measurable, respectively progressively measurable, state process supplies the matching
measurability of the integrands.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- Joint measurability of the diffusion integrand along a jointly measurable state process. -/
theorem measurable_sigma_comp_state {n d : ℕ} {ν : MeasureTheory.Measure E}
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {X : ℝ → Ω → (Fin n → ℝ)} (hX : Measurable (Function.uncurry X)) (i : Fin n) (j : Fin d) :
    Measurable (Function.uncurry fun ω s => coeffs.σ s (X s ω) i j) :=
  ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hReg.2.1)).comp
    (measurable_snd.prodMk (hX.comp (measurable_snd.prodMk measurable_fst)))
/-- Joint measurability of the jump integrand along a jointly measurable state process. -/
theorem measurable_gamma_comp_state {n d : ℕ} {ν : MeasureTheory.Measure E}
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {X : ℝ → Ω → (Fin n → ℝ)} (hX : Measurable (Function.uncurry X)) (i : Fin n) :
    Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i :=
  ((measurable_pi_apply i).comp hReg.2.2.1).comp
    ((measurable_fst.comp measurable_snd).prodMk
      ((hX.comp ((measurable_fst.comp measurable_snd).prodMk measurable_fst)).prodMk
        (measurable_snd.comp measurable_snd)))
/-- **Linear growth of the drift coefficient in the state**, read off the Lipschitz hypothesis
by comparing with the state `0`. -/
theorem sq_mu_le {n d : ℕ} {ν : MeasureTheory.Measure E}
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E) {L : ℝ}
    (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (s : ℝ) (x : Fin n → ℝ) (i : Fin n) :
    (coeffs.μ s x i) ^ 2
      ≤ 2 * ‖coeffs.μ s 0‖ ^ 2 + 2 * (L ^ 2 * ∑ i', (x i') ^ 2) := by
  have hL := hLip.2.1 s x 0
  have hcoord : |coeffs.μ s x i - coeffs.μ s 0 i| ≤ ‖coeffs.μ s x - coeffs.μ s 0‖ := by
    simpa [Real.norm_eq_abs, Pi.sub_apply] using norm_le_pi_norm (coeffs.μ s x - coeffs.μ s 0) i
  have h0 : |coeffs.μ s 0 i| ≤ ‖coeffs.μ s 0‖ := by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm (coeffs.μ s 0) i
  have hx : ‖x - 0‖ ^ 2 ≤ ∑ i', (x i') ^ 2 := by
    rw [sub_zero]; exact sq_norm_le_sum_sq x
  have hnormsq : ‖coeffs.μ s x - coeffs.μ s 0‖ ^ 2 ≤ L ^ 2 * ∑ i', (x i') ^ 2 := by
    have h1 : ‖coeffs.μ s x - coeffs.μ s 0‖ ^ 2 ≤ L ^ 2 * ‖x - 0‖ ^ 2 := by
      nlinarith [norm_nonneg (coeffs.μ s x - coeffs.μ s 0), norm_nonneg (x - 0), hLip.1]
    exact h1.trans (mul_le_mul_of_nonneg_left hx (sq_nonneg L))
  have hdiff : (coeffs.μ s x i - coeffs.μ s 0 i) ^ 2 ≤ L ^ 2 * ∑ i', (x i') ^ 2 := by
    nlinarith [hcoord, abs_nonneg (coeffs.μ s x i - coeffs.μ s 0 i),
      sq_abs (coeffs.μ s x i - coeffs.μ s 0 i), norm_nonneg (coeffs.μ s x - coeffs.μ s 0)]
  have hzero : (coeffs.μ s 0 i) ^ 2 ≤ ‖coeffs.μ s 0‖ ^ 2 := by
    nlinarith [h0, abs_nonneg (coeffs.μ s 0 i), sq_abs (coeffs.μ s 0 i),
      norm_nonneg (coeffs.μ s 0)]
  nlinarith [sq_nonneg (coeffs.μ s x i - 2 * coeffs.μ s 0 i)]
end LevyStochCalc.Ito.Picard


