-- Prove2me | Definitions.Def_LevyStochCalc_Ito_JumpCoefficientPredictableLeftLim_F000
-- name    : LevyStochCalc_Ito_JumpCoefficientPredictableLeftLim_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:59:42.573195+00:00
-- url     : https://prove2.me/theorems/f0b13d50-47d1-4255-ba7e-701c73f10f43
-- title:
--   Source declarations: LevyStochCalc.Ito.JumpCoefficientPredictableLeftLim
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.JumpCoefficientPredictableLeftLim. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpCoefficientPredictableCriteria_F001
import Definitions.Def_LevyStochCalc_Ito_JumpCoefficientPredictableCriteria_F002
import Definitions.Def_LevyStochCalc_Ito_JumpCoefficientPredictableCriteria_F003
import Definitions.Def_LevyStochCalc_Ito_JumpSplittingLeftLim_F000

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

/-- The left limits of the path of a jump diffusion, cut to the positive times. -/
noncomputable def leftLimPathPos (X : Setting.JumpDiffusion W N coeffs x₀) (s : ℝ) (ω : Ω) :
    Fin n → ℝ := if 0 < s then leftLimPath X s ω else 0
/-- The left limits at a time of an adapted path having left limits there are known at that
time. -/
theorem measurable_leftLimPath (X : Setting.JumpDiffusion W N coeffs x₀)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hXadapt : ∀ t : ℝ, Measurable[ℱ t] (X.X t)) {t : ℝ}
    (hleft : ∀ (ω : Ω) (i : Fin n), ∃ L : ℝ, Tendsto (fun s => X.X s ω i) (𝓝[<] t) (𝓝 L)) :
    Measurable[ℱ t] (leftLimPath X t) := by
  refine (@measurable_pi_iff Ω (Fin n) (fun _ => ℝ) (ℱ t) inferInstance
    (leftLimPath X t)).mpr fun i => ?_
  have hrw : (fun ω => leftLimPath X t ω i)
      = fun ω => limsup (fun k : ℕ => X.X (leftGridPoint k t) ω i) atTop := by
    funext ω
    exact (((tendsto_nhdsLT_leftLimPath (fun j => hleft ω j) i).comp
      (_root_.Prove2MeSourceProof.h_7933289efea3e77799cfdcda t)).limsup_eq).symm
  rw [hrw]
  refine Measurable.limsup fun k => ?_
  have hm : Measurable[ℱ (leftGridPoint k t)] fun ω => X.X (leftGridPoint k t) ω i :=
    (measurable_pi_apply i).comp (hXadapt (leftGridPoint k t))
  exact hm.mono (ℱ.mono (leftGridPoint_lt k t).le) le_rfl
/-- **The left limits of a path having left limits at the positive times are left-continuous
there.** -/
theorem tendsto_nhdsLT_leftLimPath_self (X : Setting.JumpDiffusion W N coeffs x₀) {ω : Ω}
    (hleft : ∀ t : ℝ, 0 < t → ∀ i : Fin n,
      ∃ L : ℝ, Tendsto (fun s => X.X s ω i) (𝓝[<] t) (𝓝 L))
    {t : ℝ} (ht : 0 < t) :
    Tendsto (fun u => leftLimPath X u ω) (𝓝[<] t) (𝓝 (leftLimPath X t ω)) := by
  refine tendsto_pi_nhds.mpr fun i => ?_
  refine Metric.tendsto_nhdsWithin_nhds.mpr fun ε hε => ?_
  obtain ⟨δ, hδ, hδ'⟩ := Metric.tendsto_nhdsWithin_nhds.mp
    (tendsto_nhdsLT_leftLimPath (hleft t ht) i) (ε / 2) (by linarith)
  refine ⟨min δ t, lt_min hδ ht, fun {u} hu hdu => ?_⟩
  have hut : u < t := hu
  have hdist : dist u t = t - u := by
    rw [Real.dist_eq, abs_of_nonpos (by linarith : u - t ≤ 0)]
    ring
  rw [hdist] at hdu
  have hupos : 0 < u := by
    have h := lt_of_lt_of_le hdu (min_le_right δ t)
    linarith
  have hδu : t - δ < u := by
    have h := lt_of_lt_of_le hdu (min_le_left δ t)
    linarith
  have hconv : Tendsto (fun s => X.X s ω i) (𝓝[<] u) (𝓝 (leftLimPath X u ω i)) :=
    tendsto_nhdsLT_leftLimPath (hleft u hupos) i
  have hev : ∀ᶠ x in 𝓝[<] u, dist (X.X x ω i) (leftLimPath X t ω i) ≤ ε / 2 := by
    filter_upwards [Ioo_mem_nhdsLT hδu] with x hx
    have hxt : x < t := lt_trans hx.2 hut
    have hdx : dist x t < δ := by
      rw [Real.dist_eq, abs_of_nonpos (by linarith : x - t ≤ 0)]
      linarith [hx.1]
    exact (hδ' (Set.mem_Iio.mpr hxt) hdx).le
  have hle : dist (leftLimPath X u ω i) (leftLimPath X t ω i) ≤ ε / 2 :=
    le_of_tendsto (hconv.dist tendsto_const_nhds) hev
  linarith
end LevyStochCalc.Ito.JumpSplitting


