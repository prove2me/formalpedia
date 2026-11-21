-- Prove2me | Definitions.Def_SourceProof_c5cf45bd11a3d53a89dd04c6
-- name    : SourceProof_c5cf45bd11a3d53a89dd04c6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:04:17.97488+00:00
-- url     : https://prove2.me/theorems/5aeb7ea0-c89b-475e-8069-e23549ce4d5f
-- title:
--   LevyStochCalc source module: SourceProof_c5cf45bd11a3d53a89dd04c6
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpSplitting.measurable_predictableSigma_leftLimPathPos` comes from the `LevyStochCalc.Ito.JumpCoefficientPredictableLeftLim` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpCoefficientPredictableLeftLim_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The jump coefficient read at the left limits of the path

The left limits of a path are the limit along a dyadic grid of the path itself, so for a path
having left limits at the positive times they are known at the current time whenever the path is
adapted and they are left-continuous there; cut to the positive times they are predictable, hence
the jump coefficient of a jump diffusion evaluated at them is predictable on the time–mark space.

## References

* Protter, *Stochastic Integration and Differential Equations*, 2005, §III.2.
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §II.3.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.JumpSplitting

open LevyStochCalc.Probability

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}


theorem _root_.Prove2MeSourceProof.h_c5cf45bd11a3d53a89dd04c6 (X : Setting.JumpDiffusion W N coeffs x₀)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hXadapt : ∀ t : ℝ, Measurable[ℱ t] (X.X t))
    (hleft : ∀ (ω : Ω) (t : ℝ), 0 < t → ∀ i : Fin n,
      ∃ L : ℝ, Tendsto (fun s => X.X s ω i) (𝓝[<] t) (𝓝 L)) :
    Measurable[predictableSigma ℱ] fun p : ℝ × Ω => leftLimPathPos X p.1 p.2 := by
  classical
  refine (@measurable_pi_iff (ℝ × Ω) (Fin n) (fun _ => ℝ) (LevyStochCalc.Probability.predictableSigma ℱ) inferInstance
    (fun p : ℝ × Ω => LevyStochCalc.Ito.JumpSplitting.leftLimPathPos X p.1 p.2)).mpr fun i => ?_
  refine LevyStochCalc.Probability.measurable_predictableSigma_of_tendsto_leftGridPoint
    (Z := fun t ω => if 0 < t then X.X t ω i else 0)
    (Y := fun t ω => LevyStochCalc.Ito.JumpSplitting.leftLimPathPos X t ω i) (fun t => ?_) (fun s ω => ?_)
  · by_cases h : (0 : ℝ) < t
    · have hm : Measurable[ℱ t] fun ω => X.X t ω i := (measurable_pi_apply i).comp (hXadapt t)
      simpa [h] using hm
    · simp only [if_neg h]
      exact measurable_const
  · by_cases hs : (0 : ℝ) < s
    · have hnhds : Tendsto (fun k : ℕ => LevyStochCalc.Probability.leftGridPoint k s) atTop (𝓝 s) :=
        (_root_.Prove2MeSourceProof.h_7933289efea3e77799cfdcda s).mono_right nhdsWithin_le_nhds
      have hev : ∀ᶠ k : ℕ in atTop, 0 < LevyStochCalc.Probability.leftGridPoint k s := hnhds.eventually (lt_mem_nhds hs)
      have hconv : Tendsto (fun k : ℕ => X.X (LevyStochCalc.Probability.leftGridPoint k s) ω i) atTop
          (𝓝 (LevyStochCalc.Ito.JumpSplitting.leftLimPath X s ω i)) :=
        (LevyStochCalc.Ito.JumpSplitting.tendsto_nhdsLT_leftLimPath (hleft ω s hs) i).comp (_root_.Prove2MeSourceProof.h_7933289efea3e77799cfdcda s)
      have hcong : (fun k : ℕ => X.X (LevyStochCalc.Probability.leftGridPoint k s) ω i)
          =ᶠ[atTop] fun k : ℕ =>
            if 0 < LevyStochCalc.Probability.leftGridPoint k s then X.X (LevyStochCalc.Probability.leftGridPoint k s) ω i else 0 := by
        filter_upwards [hev] with k hk
        rw [if_pos hk]
      simpa [LevyStochCalc.Ito.JumpSplitting.leftLimPathPos, hs] using hconv.congr' hcong
    · have h0 : ∀ k : ℕ, ¬(0 < LevyStochCalc.Probability.leftGridPoint k s) := fun k hk =>
        hs (lt_trans hk (LevyStochCalc.Probability.leftGridPoint_lt k s))
      have hzero : (fun k : ℕ =>
          if 0 < LevyStochCalc.Probability.leftGridPoint k s then X.X (LevyStochCalc.Probability.leftGridPoint k s) ω i else 0)
          = fun _ : ℕ => (0 : ℝ) := by
        funext k
        exact if_neg (h0 k)
      rw [hzero]
      simp [LevyStochCalc.Ito.JumpSplitting.leftLimPathPos, hs]
end LevyStochCalc.Ito.JumpSplitting


