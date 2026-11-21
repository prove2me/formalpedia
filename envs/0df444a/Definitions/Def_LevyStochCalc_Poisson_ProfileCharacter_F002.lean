-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_ProfileCharacter_F002
-- name    : LevyStochCalc_Poisson_ProfileCharacter_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T15:16:50.597858+00:00
-- url     : https://prove2.me/theorems/aed2bcff-491e-4233-91f9-d4acd1916377
-- title:
--   Source declarations: LevyStochCalc.Poisson.ProfileCharacter
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.ProfileCharacter. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
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

/-- The increment of the character of a real variable. -/
private theorem norm_exp_I_mul_sub_le (u x y : ℝ) :
    ‖Complex.exp (Complex.I * ((u * x : ℝ) : ℂ))
      - Complex.exp (Complex.I * ((u * y : ℝ) : ℂ))‖ ≤ |u| * |x - y| := by
  have h1 : Complex.exp (Complex.I * ((u * x : ℝ) : ℂ))
      = Complex.exp (Complex.I * ((u * y : ℝ) : ℂ))
        * Complex.exp (Complex.I * ((u * (x - y) : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have h2 : Complex.exp (Complex.I * ((u * x : ℝ) : ℂ))
      - Complex.exp (Complex.I * ((u * y : ℝ) : ℂ))
      = Complex.exp (Complex.I * ((u * y : ℝ) : ℂ))
        * (Complex.exp (Complex.I * ((u * (x - y) : ℝ) : ℂ)) - 1) := by
    rw [h1]; ring
  rw [h2, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
  rw [Real.norm_eq_abs, abs_mul]
/-- The first absolute moment of a square-integrable variable on a probability space. -/
private theorem integral_abs_le_sqrt {F : Ω → ℝ} (hF : MemLp F 2 P) :
    ∫ ω, |F ω| ∂P ≤ Real.sqrt (∫ ω, F ω ^ 2 ∂P) := by
  have h := integral_abs_mul_le_sqrt hF (memLp_const (μ := P) (p := 2) (1 : ℝ))
  simpa using h
/-- The character of a real variable is continuous along `L²(P)` convergence. -/
private theorem tendsto_integral_exp_I_mul {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (hX : ∀ n, MemLp (X n) 2 P) (hY : MemLp Y 2 P)
    (hconv : Tendsto (fun n => eLpNorm (fun ω => X n ω - Y ω) 2 P) atTop (nhds 0)) (u : ℝ) :
    Tendsto (fun n => ∫ ω, Complex.exp (Complex.I * ((u * X n ω : ℝ) : ℂ)) ∂P) atTop
      (nhds (∫ ω, Complex.exp (Complex.I * ((u * Y ω : ℝ) : ℂ)) ∂P)) := by
  have hcexp : Continuous fun t : ℝ => Complex.exp (Complex.I * (t : ℂ)) := by fun_prop
  have hint : ∀ Z : Ω → ℝ, MemLp Z 2 P →
      Integrable (fun ω => Complex.exp (Complex.I * ((u * Z ω : ℝ) : ℂ))) P := by
    intro Z hZ
    refine Integrable.mono' (g := fun _ => (1 : ℝ)) (integrable_const 1)
      (hcexp.comp_aestronglyMeasurable (hZ.1.const_mul u)) (Eventually.of_forall fun ω => ?_)
    rw [Complex.norm_exp_I_mul_ofReal]
  have hDm : ∀ n, MemLp (fun ω => X n ω - Y ω) 2 P := fun n => (hX n).sub hY
  have hdconv : Tendsto (fun n => ∫ ω, (X n ω - Y ω) ^ 2 ∂P) atTop (nhds 0) := by
    have hEq : ∀ n, ∫ ω, (X n ω - Y ω) ^ 2 ∂P
        = ((eLpNorm (fun ω => X n ω - Y ω) 2 P).toReal) ^ 2 := fun n =>
      integral_sq_eq_toReal_eLpNorm_sq (hDm n)
    simp_rw [hEq]
    have h1 : Tendsto (fun n => (eLpNorm (fun ω => X n ω - Y ω) 2 P).toReal) atTop (nhds 0) := by
      have h := (ENNReal.tendsto_toReal (a := 0) (by simp)).comp hconv
      simpa [Function.comp_def] using h
    simpa using h1.pow 2
  have hbound : ∀ n, ‖(∫ ω, Complex.exp (Complex.I * ((u * X n ω : ℝ) : ℂ)) ∂P)
      - ∫ ω, Complex.exp (Complex.I * ((u * Y ω : ℝ) : ℂ)) ∂P‖
      ≤ |u| * Real.sqrt (∫ ω, (X n ω - Y ω) ^ 2 ∂P) := by
    intro n
    have hintD : Integrable (fun ω => |u| * |X n ω - Y ω|) P :=
      (((hDm n).integrable one_le_two).abs).const_mul _
    rw [← integral_sub (hint _ (hX n)) (hint _ hY)]
    refine (norm_integral_le_integral_norm _).trans ?_
    calc ∫ ω, ‖Complex.exp (Complex.I * ((u * X n ω : ℝ) : ℂ))
          - Complex.exp (Complex.I * ((u * Y ω : ℝ) : ℂ))‖ ∂P
        ≤ ∫ ω, |u| * |X n ω - Y ω| ∂P := by
          refine integral_mono (((hint _ (hX n)).sub (hint _ hY)).norm) hintD fun ω => ?_
          exact norm_exp_I_mul_sub_le u (X n ω) (Y ω)
      _ = |u| * ∫ ω, |X n ω - Y ω| ∂P := integral_const_mul _ _
      _ ≤ |u| * Real.sqrt (∫ ω, (X n ω - Y ω) ^ 2 ∂P) := by
          gcongr
          exact integral_abs_le_sqrt (hDm n)
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun n => norm_nonneg _) hbound ?_)
  simpa using (hdconv.sqrt).const_mul |u|
end LevyStochCalc.Poisson


