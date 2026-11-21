-- Prove2me | Definitions.Def_SourceProof_722eb9b2cd962b654329cb6c
-- name    : SourceProof_722eb9b2cd962b654329cb6c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T16:22:39.770402+00:00
-- url     : https://prove2.me/theorems/51046976-3bb5-4b63-b157-a67ce25c4bae
-- title:
--   LevyStochCalc source module: SourceProof_722eb9b2cd962b654329cb6c
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.integral_exp_I_mul_of_tendsto_stepIntegral` comes from the `LevyStochCalc.Poisson.ProfileCharacter` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_ProfileCharacter_F002
import Definitions.Def_SourceProof_e7a43d4e853b8f43d6d514ad
import Definitions.Def_SourceProof_f993fbc9ff9a1b70b006b96e

open private tendsto_integral_exp_I_mul from Definitions.Def_LevyStochCalc_Poisson_ProfileCharacter_F002
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


theorem _root_.Prove2MeSourceProof.h_722eb9b2cd962b654329cb6c (N : PoissonRandomMeasure P ν)
    (G : ℕ → SimpleProfile E ν) {f : E → ℝ} (hf : MemLp f 2 ν) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) {J : Ω → ℝ} (hJ : MemLp J 2 P)
    (hGf : Tendsto (fun n => eLpNorm (fun e => (G n).toFun e - f e) 2 ν) atTop (nhds 0))
    (hJlim : Tendsto (fun n => eLpNorm (fun ω => (G n).stepIntegral N a b ω - J ω) 2 P)
      atTop (nhds 0)) (u : ℝ) :
    ∫ ω, Complex.exp (Complex.I * ((u * J ω : ℝ) : ℂ)) ∂P
      = Complex.exp (((b - a : ℝ) : ℂ) * ∫ e, levyCharIntegrand u (f e) ∂ν) := by
  have hLHS : Tendsto (fun n => ∫ ω,
      Complex.exp (Complex.I * ((u * (G n).stepIntegral N a b ω : ℝ) : ℂ)) ∂P) atTop
      (nhds (∫ ω, Complex.exp (Complex.I * ((u * J ω : ℝ) : ℂ)) ∂P)) :=
    tendsto_integral_exp_I_mul (fun n => (G n).memLp_stepIntegral N ha b) hJ hJlim u
  have hRHS : Tendsto (fun n => Complex.exp (((b - a : ℝ) : ℂ)
      * ∫ e, LevyStochCalc.Poisson.levyCharIntegrand u ((G n).toFun e) ∂ν)) atTop
      (nhds (Complex.exp (((b - a : ℝ) : ℂ) * ∫ e, LevyStochCalc.Poisson.levyCharIntegrand u (f e) ∂ν))) :=
    (Complex.continuous_exp.tendsto _).comp
      ((_root_.Prove2MeSourceProof.h_f993fbc9ff9a1b70b006b96e u (fun n => (G n).memLp_toFun) hf hGf).const_mul _)
  exact tendsto_nhds_unique hLHS
    (hRHS.congr fun n => ((_root_.Prove2MeSourceProof.h_e7a43d4e853b8f43d6d514ad (G n)) N ha hab u).symm)
end LevyStochCalc.Poisson


