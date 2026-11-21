-- Prove2me | Definitions.Def_SourceProof_39bcf7b6426eb7b206aa98c5
-- name    : SourceProof_39bcf7b6426eb7b206aa98c5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T16:03:39.231422+00:00
-- url     : https://prove2.me/theorems/b3efc183-64da-43fc-a67b-782fb48f89cd
-- title:
--   LevyStochCalc source module: SourceProof_39bcf7b6426eb7b206aa98c5
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.exists_simpleProfile_tendsto_L2` comes from the `LevyStochCalc.Poisson.SimpleProfile` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_SimpleProfile_F002

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

/-! ### The compensated integral of a simple profile over a step -/

variable (N : PoissonRandomMeasure P ν)

/-! ### Simple profiles from simple functions -/

end SimpleProfile

/-! ### Approximation of a square-integrable mark profile -/

omit [SigmaFinite ν] in

theorem _root_.Prove2MeSourceProof.h_39bcf7b6426eb7b206aa98c5 {f : E → ℝ} (hf : MemLp f 2 ν) {Cb : ℝ}
    (hb : ∀ e, |f e| ≤ Cb) :
    ∃ G : ℕ → SimpleProfile E ν, (∀ n e, |(G n).toFun e| ≤ Cb) ∧
      Filter.Tendsto (fun n => eLpNorm (fun e => (G n).toFun e - f e) 2 ν)
        Filter.atTop (nhds 0) := by
  rcases le_or_gt 0 Cb with hCb | hCb
  · have h₀ : (0 : ℝ) ∈ Set.Icc (-Cb) Cb := Set.mem_Icc.2 ⟨by linarith, hCb⟩
    set f₀ : E → ℝ := fun e => max (-Cb) (min Cb (hf.1.mk f e)) with hf₀def
    have hf₀m : Measurable f₀ :=
      measurable_const.max (measurable_const.min hf.1.stronglyMeasurable_mk.measurable)
    have hf₀s : ∀ e, f₀ e ∈ Set.Icc (-Cb) Cb := fun e =>
      Set.mem_Icc.2 ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
    have hf₀ae : f₀ =ᵐ[ν] f := by
      filter_upwards [hf.1.ae_eq_mk] with e he
      have h1 := abs_le.1 (hb e)
      simp only [hf₀def, ← he]
      rw [min_eq_right h1.2, max_eq_right h1.1]
    have hf₀L : MemLp f₀ 2 ν := MemLp.ae_eq hf₀ae.symm hf
    have happrox : ∀ n, MemLp (SimpleFunc.approxOn f₀ hf₀m (Set.Icc (-Cb) Cb) 0 h₀ n) 2 ν :=
      fun n => SimpleFunc.memLp_approxOn hf₀m hf₀L h₀ (by simp) n
    refine ⟨fun n => LevyStochCalc.Poisson.SimpleProfile.ofSimpleFunc (happrox n), fun n e => ?_, ?_⟩
    · rw [LevyStochCalc.Poisson.SimpleProfile.toFun_ofSimpleFunc]
      exact abs_le.2 (Set.mem_Icc.1 (SimpleFunc.approxOn_mem hf₀m h₀ n e))
    · have htend := SimpleFunc.tendsto_approxOn_Lp_eLpNorm hf₀m h₀ (p := 2) (by norm_num)
        (Filter.Eventually.of_forall fun e => subset_closure (hf₀s e))
        (by simpa using hf₀L.eLpNorm_lt_top)
      refine htend.congr fun n => eLpNorm_congr_ae ?_
      filter_upwards [hf₀ae] with e he
      simp [he]
  · have hE : IsEmpty E := ⟨fun e => absurd ((abs_nonneg (f e)).trans (hb e)) (not_le.2 hCb)⟩
    have hν0 : ν = 0 := by
      ext s _
      rw [Set.eq_empty_of_isEmpty s]
      simp
    exact ⟨fun _ => ⟨0, fun k => k.elim0, fun k => k.elim0, fun k => k.elim0,
      fun k => k.elim0, fun k => k.elim0⟩, fun _ e => (hE.false e).elim,
      by simp [hν0]⟩
/-! ### Convergence of the compensated step integrals -/

end LevyStochCalc.Poisson


