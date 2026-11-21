-- Prove2me | Definitions.Def_SourceProof_1aa328a9a0337e8548a6f052
-- name    : SourceProof_1aa328a9a0337e8548a6f052
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T16:03:15.119408+00:00
-- url     : https://prove2.me/theorems/7ce1fb5f-bbfd-4b41-a58b-368c6e239bf0
-- title:
--   LevyStochCalc source module: SourceProof_1aa328a9a0337e8548a6f052
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.exists_memLp_tendsto_stepIntegral` comes from the `LevyStochCalc.Poisson.SimpleProfile` module. The staged Lean declaration includes its source proof and dependency references.
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

/-! ### Convergence of the compensated step integrals -/


theorem _root_.Prove2MeSourceProof.h_1aa328a9a0337e8548a6f052 (N : PoissonRandomMeasure P ν)
    (G : ℕ → SimpleProfile E ν) {f : E → ℝ} (hf : MemLp f 2 ν) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b)
    (hG : Filter.Tendsto (fun n => eLpNorm (fun e => (G n).toFun e - f e) 2 ν)
      Filter.atTop (nhds 0)) :
    ∃ J : Ω → ℝ, MemLp J 2 P ∧
      Filter.Tendsto (fun n => eLpNorm (fun ω => (G n).stepIntegral N a b ω - J ω) 2 P)
        Filter.atTop (nhds 0) := by
  set u : ℕ → Lp ℝ 2 P := fun n => ((G n).memLp_stepIntegral N ha b).toLp _
  have hcoe : ∀ n, ⇑(u n) =ᵐ[P] (G n).stepIntegral N a b :=
    fun n => MemLp.coeFn_toLp ((G n).memLp_stepIntegral N ha b)
  have hstep : ∀ m n, eLpNorm (⇑(u m) - ⇑(u n)) 2 P
      = ENNReal.ofReal (Real.sqrt (b - a))
        * eLpNorm (fun e => (G m).toFun e - (G n).toFun e) 2 ν := by
    intro m n
    rw [← LevyStochCalc.Poisson.SimpleProfile.eLpNorm_stepIntegral_sub N (G m) (G n) ha hab]
    refine eLpNorm_congr_ae ?_
    filter_upwards [hcoe m, hcoe n] with ω h1 h2
    simp [h1, h2]
  have hbound : ∀ m n, eLpNorm (fun e => (G m).toFun e - (G n).toFun e) 2 ν
      ≤ eLpNorm (fun e => (G m).toFun e - f e) 2 ν
        + eLpNorm (fun e => (G n).toFun e - f e) 2 ν := by
    intro m n
    have hm : MemLp (fun e => (G m).toFun e - f e) 2 ν := (G m).memLp_toFun.sub hf
    have hn : MemLp (fun e => (G n).toFun e - f e) 2 ν := (G n).memLp_toFun.sub hf
    calc eLpNorm (fun e => (G m).toFun e - (G n).toFun e) 2 ν
        = eLpNorm ((fun e => (G m).toFun e - f e) - fun e => (G n).toFun e - f e) 2 ν := by
          refine eLpNorm_congr_ae (Filter.Eventually.of_forall fun e => ?_)
          simp only [Pi.sub_apply]
          ring
      _ ≤ _ := eLpNorm_sub_le hm.aestronglyMeasurable hn.aestronglyMeasurable one_le_two
  have hfst : Filter.Tendsto
      (fun mn : ℕ × ℕ => eLpNorm (fun e => (G mn.1).toFun e - f e) 2 ν)
      Filter.atTop (nhds 0) := by
    rw [← Filter.prod_atTop_atTop_eq]
    exact hG.comp Filter.tendsto_fst
  have hsnd : Filter.Tendsto
      (fun mn : ℕ × ℕ => eLpNorm (fun e => (G mn.2).toFun e - f e) 2 ν)
      Filter.atTop (nhds 0) := by
    rw [← Filter.prod_atTop_atTop_eq]
    exact hG.comp Filter.tendsto_snd
  have hsum : Filter.Tendsto (fun mn : ℕ × ℕ => ENNReal.ofReal (Real.sqrt (b - a))
      * (eLpNorm (fun e => (G mn.1).toFun e - f e) 2 ν
        + eLpNorm (fun e => (G mn.2).toFun e - f e) 2 ν)) Filter.atTop (nhds 0) := by
    have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (Real.sqrt (b - a)))
      (hfst.add hsnd) (Or.inr ENNReal.ofReal_ne_top)
    simpa using this
  have hcauchy : CauchySeq u := by
    rw [Lp.cauchySeq_Lp_iff_cauchySeq_eLpNorm]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun _ => by simp) fun mn => ?_
    rw [hstep]
    exact _root_.mul_le_mul_right (hbound mn.1 mn.2) _
  obtain ⟨J, hJ⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨⇑J, Lp.memLp J, ?_⟩
  refine ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' u J).1 hJ).congr fun n => eLpNorm_congr_ae ?_
  filter_upwards [hcoe n] with ω h1
  simp [h1]
end LevyStochCalc.Poisson


