-- Prove2me | Definitions.Def_SourceProof_adfffb5c0bed4c951bccc3c4
-- name    : SourceProof_adfffb5c0bed4c951bccc3c4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T15:10:51.389666+00:00
-- url     : https://prove2.me/theorems/a5d7057f-be2a-4a8d-93ab-b8b06da698a3
-- title:
--   LevyStochCalc source module: SourceProof_adfffb5c0bed4c951bccc3c4
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.SimpleProfile.integral_toFun_mul` comes from the `LevyStochCalc.Poisson.SimpleProfile` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_SimpleProfile_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Simple mark profiles and their compensated step integrals

A *simple mark profile* for an intensity `ν` on the mark space is a finite family of pairwise
disjoint mark sets of finite intensity carrying constant coefficients, `∑ₖ cₖ 𝟙_{Bₖ}`. Every
square-integrable mark profile is the `L²(ν)` limit of simple profiles, obtained from the nonzero
level sets of square-integrable simple functions approximating it in `L²(ν)`; a bounded one is
the limit of simple profiles obeying the same bound, obtained from the simple functions
approximating it inside the interval the bound cuts out.

The compensated integral of a simple profile over the step `(a, b]` is
`∑ₖ cₖ Ñ((a, b] × Bₖ)`. The `L²(P)` pairing of two such integrals over a common step is
`(b − a) ∫ f g dν`, so profiles converging in `L²(ν)` have compensated integrals converging in
`L²(P)`.

## Main definitions

* `LevyStochCalc.Poisson.SimpleProfile` — a simple mark profile.
* `LevyStochCalc.Poisson.SimpleProfile.toFun` — the function it carries.
* `LevyStochCalc.Poisson.SimpleProfile.stepIntegral` — its compensated integral over a step.

## Main statements

* `LevyStochCalc.Poisson.exists_simpleProfile_tendsto_L2_of_memLp` — approximation of a
  square-integrable mark profile by simple profiles.
* `LevyStochCalc.Poisson.exists_simpleProfile_tendsto_L2` — approximation of a bounded
  square-integrable mark profile by simple profiles obeying the same bound.
* `LevyStochCalc.Poisson.SimpleProfile.integral_stepIntegral_mul` — the `L²(P)` pairing of two
  compensated step integrals.
* `LevyStochCalc.Poisson.SimpleProfile.eLpNorm_stepIntegral_sub` — the isometry
  `‖J(f) − J(g)‖_{L²(P)} = √(b − a) ‖f − g‖_{L²(ν)}`.
* `LevyStochCalc.Poisson.exists_memLp_tendsto_stepIntegral` — convergence of the compensated
  integrals in `L²(P)`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

namespace SimpleProfile

omit [SigmaFinite ν] in

theorem _root_.Prove2MeSourceProof.h_adfffb5c0bed4c951bccc3c4 (G G' : SimpleProfile E ν) :
    ∫ e, G.toFun e * G'.toFun e ∂ν
      = ∑ k, ∑ l, G.c k * G'.c l * (ν (G.B k ∩ G'.B l)).toReal := by
  have hmeas : ∀ (k : Fin G.K) (l : Fin G'.K), MeasurableSet (G.B k ∩ G'.B l) :=
    fun k l => (G.B_measurable k).inter (G'.B_measurable l)
  have hfin : ∀ (k : Fin G.K) (l : Fin G'.K), ν (G.B k ∩ G'.B l) ≠ ⊤ :=
    fun k l => ne_top_of_le_ne_top (G.B_finite k) (measure_mono Set.inter_subset_left)
  have hint : ∀ (k : Fin G.K) (l : Fin G'.K),
      Integrable (fun e => G.c k * G'.c l
        * (G.B k ∩ G'.B l).indicator (fun _ => (1 : ℝ)) e) ν := fun k l =>
    Integrable.const_mul (memLp_one_iff_integrable.1
      (memLp_indicator_const 1 (hmeas k l) (1 : ℝ) (Or.inr (hfin k l)))) _
  simp_rw [LevyStochCalc.Poisson.SimpleProfile.toFun_mul]
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hint k l]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finsetSum _ fun l _ => hint k l]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_const_mul, integral_indicator_const (1 : ℝ) (hmeas k l), smul_eq_mul, mul_one,
    measureReal_def]
/-! ### The compensated integral of a simple profile over a step -/

variable (N : PoissonRandomMeasure P ν)

/-! ### Simple profiles from simple functions -/

end SimpleProfile

/-! ### Approximation of a square-integrable mark profile -/

/-! ### Convergence of the compensated step integrals -/

end LevyStochCalc.Poisson


