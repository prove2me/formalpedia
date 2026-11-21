-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_ProfileCharacter_F001
-- name    : LevyStochCalc_Poisson_ProfileCharacter_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T15:15:07.745533+00:00
-- url     : https://prove2.me/theorems/4a3b8237-04a0-4153-84b3-e55d8ce40c72
-- title:
--   Source declarations: LevyStochCalc.Poisson.ProfileCharacter
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.ProfileCharacter. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_ProfileCharacter_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The character of a compensated step integral of a mark profile

The count of a Poisson random measure on a region of finite intensity is Poisson, so the
character of the compensated count carries the Lévy–Khintchine integrand `e^{iuc} - 1 - iuc`
at the coefficient `c`. A simple mark profile pairs pairwise-disjoint mark sets with constant
coefficients, so over a step its compensated integral is a sum of independent compensated
counts and its character is the product of the counts' characters,

  `E[exp (i u J(f))] = exp ((b - a) ∫ (exp (i u f) - 1 - i u f) dν)`.

The right-hand side is continuous along `L²(ν)` convergence of the profile, so the identity
transfers to a profile approximated by simple ones together with any `L²(P)` limit of their
compensated step integrals.

## Main definitions

* `LevyStochCalc.Poisson.levyCharIntegrand` — the integrand `e^{iux} - 1 - iux`.

## Main statements

* `LevyStochCalc.Poisson.integral_exp_I_mul_compensated` — the character of a compensated
  count on a region of finite intensity.
* `LevyStochCalc.Poisson.SimpleProfile.integral_exp_I_mul_stepIntegral` — the character of the
  compensated step integral of a simple mark profile.
* `LevyStochCalc.Poisson.integrable_levyCharIntegrand` — integrability of the integrand at a
  square-integrable mark profile.
* `LevyStochCalc.Poisson.tendsto_integral_levyCharIntegrand` — continuity of the Lévy
  characteristic exponent along `L²(ν)` convergence of the profile.
* `LevyStochCalc.Poisson.integral_exp_I_mul_of_tendsto_stepIntegral` — the character of an
  `L²(P)` limit of the compensated step integrals of simple profiles converging in `L²(ν)`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-! ### The Lévy–Khintchine integrand -/

/-! ### The character of a count and of a compensated count -/

/-! ### The character at a simple mark profile -/

namespace SimpleProfile

end SimpleProfile

/-! ### Passage to a general square-integrable profile -/

omit [SigmaFinite ν] in
/-- The Lévy characteristic integrand of a square-integrable mark profile is integrable. -/
theorem integrable_levyCharIntegrand (u : ℝ) {g : E → ℝ} (hg : MemLp g 2 ν) :
    Integrable (fun e => levyCharIntegrand u (g e)) ν := by
  refine Integrable.mono' (g := fun e => 3 * u ^ 2 * g e ^ 2) (hg.integrable_sq.const_mul _)
    ((continuous_levyCharIntegrand u).comp_aestronglyMeasurable hg.1)
    (Eventually.of_forall fun e => ?_)
  calc ‖levyCharIntegrand u (g e)‖ ≤ 3 * (u * g e) ^ 2 := norm_levyCharIntegrand_le u (g e)
    _ = 3 * u ^ 2 * g e ^ 2 := by ring
/-- The second moment of a square-integrable function through its `L²` seminorm. -/
private theorem integral_sq_eq_toReal_eLpNorm_sq {α : Type*} [MeasurableSpace α]
    {m : Measure α} {F : α → ℝ} (hF : MemLp F 2 m) :
    ∫ x, F x ^ 2 ∂m = ((eLpNorm F 2 m).toReal) ^ 2 := by
  have h0 : 0 ≤ ∫ x, F x ^ 2 ∂m := integral_nonneg fun x => sq_nonneg _
  have hE : eLpNorm F 2 m = (ENNReal.ofReal (∫ x, F x ^ 2 ∂m)) ^ (1 / 2 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
      show (2 : ℝ≥0∞).toReal = 2 from by norm_num,
      ← Compensated.lintegral_sq_eq_ofReal_integral hF]
    refine congrArg (fun x : ℝ≥0∞ => x ^ (1 / 2 : ℝ)) (lintegral_congr fun x => ?_)
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
    rfl
  rw [hE, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal h0, ← Real.sqrt_eq_rpow,
    Real.sq_sqrt h0]
/-- Cauchy–Schwarz for two square-integrable real functions. -/
private theorem integral_abs_mul_le_sqrt {α : Type*} [MeasurableSpace α] {m : Measure α}
    {F H : α → ℝ} (hF : MemLp F 2 m) (hH : MemLp H 2 m) :
    ∫ x, |F x| * |H x| ∂m
      ≤ Real.sqrt (∫ x, F x ^ 2 ∂m) * Real.sqrt (∫ x, H x ^ 2 ∂m) := by
  have h2 : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by norm_num
  have hF' : MemLp (fun x => |F x|) (ENNReal.ofReal 2) m := by
    rw [h2]; simpa [Real.norm_eq_abs] using hF.norm
  have hH' : MemLp (fun x => |H x|) (ENNReal.ofReal 2) m := by
    rw [h2]; simpa [Real.norm_eq_abs] using hH.norm
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := m) (p := 2) (q := 2)
    Real.HolderConjugate.two_two (Eventually.of_forall fun x => abs_nonneg (F x))
    (Eventually.of_forall fun x => abs_nonneg (H x)) hF' hH'
  have hconv : ∀ K : α → ℝ, ∫ x, |K x| ^ (2 : ℝ) ∂m = ∫ x, K x ^ 2 ∂m := by
    intro K
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    change |K x| ^ (2 : ℝ) = K x ^ 2
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast, sq_abs]
  rw [hconv F, hconv H] at h
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  exact h
end LevyStochCalc.Poisson


