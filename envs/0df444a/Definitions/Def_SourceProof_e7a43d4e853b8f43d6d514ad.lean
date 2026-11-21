-- Prove2me | Definitions.Def_SourceProof_e7a43d4e853b8f43d6d514ad
-- name    : SourceProof_e7a43d4e853b8f43d6d514ad
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T16:05:14.519486+00:00
-- url     : https://prove2.me/theorems/5576893f-6950-4d7e-a0ad-ebe94aa87f17
-- title:
--   LevyStochCalc source module: SourceProof_e7a43d4e853b8f43d6d514ad
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.SimpleProfile.integral_exp_I_mul_stepIntegral` comes from the `LevyStochCalc.Poisson.ProfileCharacter` module. The staged Lean declaration includes its source proof and dependency references.
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


theorem _root_.Prove2MeSourceProof.h_e7a43d4e853b8f43d6d514ad (G : SimpleProfile E ν)
    (N : PoissonRandomMeasure P ν) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (u : ℝ) :
    ∫ ω, Complex.exp (Complex.I * ((u * G.stepIntegral N a b ω : ℝ) : ℂ)) ∂P
      = Complex.exp (((b - a : ℝ) : ℂ) * ∫ e, levyCharIntegrand u (G.toFun e) ∂ν) := by
  classical
  have hRm : ∀ k : Fin G.K, MeasurableSet (Set.Ioc a b ×ˢ G.B k) := fun k =>
    measurableSet_Ioc.prod (G.B_measurable k)
  have hRfin : ∀ k : Fin G.K, LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ G.B k) ≠ ⊤ := fun k => by
    rw [LevyStochCalc.Poisson.referenceIntensity_Ioc_prod' _ ha]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (G.B_finite k)
  have hRint : ∀ k : Fin G.K, (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ G.B k)).toReal
      = (b - a) * (ν (G.B k)).toReal := fun k => by
    rw [LevyStochCalc.Poisson.referenceIntensity_Ioc_prod' _ ha, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by linarith)]
  set f : Fin G.K → ℝ≥0∞ → ℂ := fun k x =>
    Complex.exp (Complex.I * (((u * G.c k)
      * (x.toReal - (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ G.B k)).toReal) : ℝ) : ℂ)) with hf
  have hfm : ∀ k, Measurable (f k) := by
    intro k
    rw [hf]
    fun_prop
  have hXi : iIndepFun
      (fun (i : ULift (Fin G.K)) (ω : Ω) => N.N ω (Set.Ioc a b ×ˢ G.B i.down)) P := by
    refine N.independent_disjoint (fun i : ULift (Fin G.K) => Set.Ioc a b ×ˢ G.B i.down)
      (fun i => hRm i.down) ?_
    intro i j hij
    refine Set.disjoint_left.2 fun p hp hq => ?_
    refine (Set.disjoint_left.1 (G.B_disjoint ?_) hp.2) hq.2
    exact fun h => hij (ULift.down_injective h)
  have hprod : ∀ ω, ∏ i : ULift (Fin G.K), f i.down (N.N ω (Set.Ioc a b ×ˢ G.B i.down))
      = Complex.exp (Complex.I * ((u * G.stepIntegral N a b ω : ℝ) : ℂ)) := by
    intro ω
    rw [hf]
    simp only
    rw [← Complex.exp_sum,
      Fintype.sum_equiv Equiv.ulift
        (fun i : ULift (Fin G.K) => Complex.I * (((u * G.c i.down)
          * ((N.N ω (Set.Ioc a b ×ˢ G.B i.down)).toReal
            - (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ G.B i.down)).toReal) : ℝ) : ℂ))
        (fun k : Fin G.K => Complex.I * (((u * G.c k)
          * ((N.N ω (Set.Ioc a b ×ˢ G.B k)).toReal
            - (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ G.B k)).toReal) : ℝ) : ℂ))
        (fun i => rfl)]
    congr 1
    rw [LevyStochCalc.Poisson.SimpleProfile.stepIntegral, Finset.mul_sum, Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [LevyStochCalc.Poisson.PoissonRandomMeasure.compensated]
    push_cast
    ring
  have hfac : ∀ k : Fin G.K, ∫ ω, f k (N.N ω (Set.Ioc a b ×ˢ G.B k)) ∂P
      = Complex.exp ((((b - a) * (ν (G.B k)).toReal : ℝ) : ℂ)
          * LevyStochCalc.Poisson.levyCharIntegrand u (G.c k)) := by
    intro k
    have hrw : ∀ ω, f k (N.N ω (Set.Ioc a b ×ˢ G.B k))
        = Complex.exp (Complex.I * (((u * G.c k)
            * N.compensated (Set.Ioc a b ×ˢ G.B k) ω : ℝ) : ℂ)) := fun ω => by
      rw [hf, LevyStochCalc.Poisson.PoissonRandomMeasure.compensated]
    simp_rw [hrw]
    rw [LevyStochCalc.Poisson.integral_exp_I_mul_compensated N (hRm k) (hRfin k) (u * G.c k), hRint k,
      LevyStochCalc.Poisson.levyCharIntegrand]
  simp_rw [← hprod]
  rw [hXi.integral_fun_prod_comp (fun i => (N.measurable_eval (hRm i.down)).aemeasurable)
      (fun i => (hfm i.down).aestronglyMeasurable)]
  rw [Fintype.prod_equiv Equiv.ulift
    (fun i : ULift (Fin G.K) => ∫ ω, f i.down (N.N ω (Set.Ioc a b ×ˢ G.B i.down)) ∂P)
    (fun k : Fin G.K => ∫ ω, f k (N.N ω (Set.Ioc a b ×ˢ G.B k)) ∂P) (fun i => rfl)]
  simp_rw [hfac]
  rw [← Complex.exp_sum, LevyStochCalc.Poisson.SimpleProfile.integral_levyCharIntegrand_toFun, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast
  ring
end SimpleProfile

/-! ### Passage to a general square-integrable profile -/

end LevyStochCalc.Poisson


