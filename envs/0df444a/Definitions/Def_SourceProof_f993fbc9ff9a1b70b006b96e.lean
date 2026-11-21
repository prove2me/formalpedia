-- Prove2me | Definitions.Def_SourceProof_f993fbc9ff9a1b70b006b96e
-- name    : SourceProof_f993fbc9ff9a1b70b006b96e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T16:15:36.645432+00:00
-- url     : https://prove2.me/theorems/34b0ade7-f473-4846-a789-ceda1e19fb6e
-- title:
--   LevyStochCalc source module: SourceProof_f993fbc9ff9a1b70b006b96e
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.tendsto_integral_levyCharIntegrand` comes from the `LevyStochCalc.Poisson.ProfileCharacter` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Batteries.Tactic.OpenPrivate
import Definitions.Def_LevyStochCalc_Poisson_ProfileCharacter_F001

open private integral_abs_mul_le_sqrt integral_sq_eq_toReal_eLpNorm_sq from Definitions.Def_LevyStochCalc_Poisson_ProfileCharacter_F001
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

theorem _root_.Prove2MeSourceProof.h_f993fbc9ff9a1b70b006b96e (u : ℝ) {g : ℕ → E → ℝ} {f : E → ℝ}
    (hg : ∀ n, MemLp (g n) 2 ν) (hf : MemLp f 2 ν)
    (hconv : Tendsto (fun n => eLpNorm (fun e => g n e - f e) 2 ν) atTop (nhds 0)) :
    Tendsto (fun n => ∫ e, levyCharIntegrand u (g n e) ∂ν) atTop
      (nhds (∫ e, levyCharIntegrand u (f e) ∂ν)) := by
  have hDm : ∀ n, MemLp (fun e => g n e - f e) 2 ν := fun n => (hg n).sub hf
  have hdconv : Tendsto (fun n => ∫ e, (g n e - f e) ^ 2 ∂ν) atTop (nhds 0) := by
    have hEq : ∀ n, ∫ e, (g n e - f e) ^ 2 ∂ν
        = ((eLpNorm (fun e => g n e - f e) 2 ν).toReal) ^ 2 := fun n =>
      integral_sq_eq_toReal_eLpNorm_sq (hDm n)
    simp_rw [hEq]
    have h1 : Tendsto (fun n => (eLpNorm (fun e => g n e - f e) 2 ν).toReal) atTop (nhds 0) := by
      have h := (ENNReal.tendsto_toReal (a := 0) (by simp)).comp hconv
      simpa [Function.comp_def] using h
    simpa using h1.pow 2
  have hbound : ∀ n, ‖(∫ e, LevyStochCalc.Poisson.levyCharIntegrand u (g n e) ∂ν)
      - ∫ e, LevyStochCalc.Poisson.levyCharIntegrand u (f e) ∂ν‖
      ≤ 3 * u ^ 2 * (∫ e, (g n e - f e) ^ 2 ∂ν)
        + u ^ 2 * Real.sqrt (∫ e, f e ^ 2 ∂ν)
          * Real.sqrt (∫ e, (g n e - f e) ^ 2 ∂ν) := by
    intro n
    have hint1 : Integrable (fun e => 3 * u ^ 2 * (g n e - f e) ^ 2) ν :=
      (hDm n).integrable_sq.const_mul _
    have hint2 : Integrable (fun e => u ^ 2 * (|f e| * |g n e - f e|)) ν := by
      refine Integrable.const_mul ?_ _
      refine ((hf.integrable_mul (hDm n)).abs).congr (Eventually.of_forall fun e => ?_)
      change |f e * (g n e - f e)| = |f e| * |g n e - f e|
      exact abs_mul _ _
    rw [← integral_sub (LevyStochCalc.Poisson.integrable_levyCharIntegrand u (hg n))
      (LevyStochCalc.Poisson.integrable_levyCharIntegrand u hf)]
    refine (norm_integral_le_integral_norm _).trans ?_
    calc ∫ e, ‖LevyStochCalc.Poisson.levyCharIntegrand u (g n e) - LevyStochCalc.Poisson.levyCharIntegrand u (f e)‖ ∂ν
        ≤ ∫ e, (3 * u ^ 2 * (g n e - f e) ^ 2 + u ^ 2 * (|f e| * |g n e - f e|)) ∂ν := by
          refine integral_mono (((LevyStochCalc.Poisson.integrable_levyCharIntegrand u (hg n)).sub
            (LevyStochCalc.Poisson.integrable_levyCharIntegrand u hf)).norm) (hint1.add hint2) fun e => ?_
          calc ‖LevyStochCalc.Poisson.levyCharIntegrand u (g n e) - LevyStochCalc.Poisson.levyCharIntegrand u (f e)‖
              ≤ 3 * (u * (g n e - f e)) ^ 2 + u ^ 2 * |f e| * |g n e - f e| :=
                LevyStochCalc.Poisson.norm_levyCharIntegrand_sub_le u (g n e) (f e)
            _ = 3 * u ^ 2 * (g n e - f e) ^ 2 + u ^ 2 * (|f e| * |g n e - f e|) := by ring
      _ = 3 * u ^ 2 * (∫ e, (g n e - f e) ^ 2 ∂ν)
            + u ^ 2 * ∫ e, |f e| * |g n e - f e| ∂ν := by
          rw [integral_add hint1 hint2, integral_const_mul, integral_const_mul]
      _ ≤ 3 * u ^ 2 * (∫ e, (g n e - f e) ^ 2 ∂ν)
            + u ^ 2 * (Real.sqrt (∫ e, f e ^ 2 ∂ν)
              * Real.sqrt (∫ e, (g n e - f e) ^ 2 ∂ν)) := by
          gcongr
          exact integral_abs_mul_le_sqrt hf (hDm n)
      _ = _ := by ring
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun n => norm_nonneg _) hbound ?_)
  have h1 : Tendsto (fun n => 3 * u ^ 2 * (∫ e, (g n e - f e) ^ 2 ∂ν)) atTop (nhds 0) := by
    simpa using hdconv.const_mul (3 * u ^ 2)
  have h2 : Tendsto (fun n => Real.sqrt (∫ e, (g n e - f e) ^ 2 ∂ν)) atTop (nhds 0) := by
    simpa using hdconv.sqrt
  have h3 : Tendsto (fun n => u ^ 2 * Real.sqrt (∫ e, f e ^ 2 ∂ν)
      * Real.sqrt (∫ e, (g n e - f e) ^ 2 ∂ν)) atTop (nhds 0) := by
    simpa using h2.const_mul (u ^ 2 * Real.sqrt (∫ e, f e ^ 2 ∂ν))
  simpa using h1.add h3
end LevyStochCalc.Poisson


