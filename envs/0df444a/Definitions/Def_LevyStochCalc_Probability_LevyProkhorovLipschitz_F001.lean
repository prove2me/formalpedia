-- Prove2me | Definitions.Def_LevyStochCalc_Probability_LevyProkhorovLipschitz_F001
-- name    : LevyStochCalc_Probability_LevyProkhorovLipschitz_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:38:15.358192+00:00
-- url     : https://prove2.me/theorems/57dafffb-b99f-4ef1-998c-811635c29455
-- title:
--   LevyStochCalc source module: LevyStochCalc.Probability.LevyProkhorovLipschitz
-- statement:
--   Exact source-faithful declarations from LevyStochCalc.Probability.LevyProkhorovLipschitz in the pinned LevyStochCalc project.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_95e0cc414c3966abf368871c
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Integrals of Lipschitz functions under the Lévy–Prokhorov metric

For probability measures `μ`, `ν` on a pseudo-metric space and a nonnegative bounded continuous
`K`-Lipschitz function `g`,
`|∫ g dμ - ∫ g dν| ≤ (K + ‖g‖) · levyProkhorovDist μ ν`.

By the layer-cake formula, `∫ g dμ` is bounded by the integral over `t ∈ (0, ‖g‖]` of the
`ν`-mass of the `ε`-thickening of `{t ≤ g}`, plus `ε ‖g‖`, whenever the Lévy–Prokhorov distance
is below `ε`. Since `g` is `K`-Lipschitz, that thickening lies inside `{t - K ε ≤ g}`, and shifting
the layer-cake integral by `K ε` costs at most `K ε`.

## Main statements

* `LevyStochCalc.Probability.thickening_setOf_le_subset` — the `ε`-thickening of a superlevel set
  `{t ≤ f}` of a `K`-Lipschitz function lies in `{t - K ε ≤ f}`.
* `LevyStochCalc.Probability.integral_le_integral_add_of_levyProkhorovEDist_lt` — the one-sided
  bound `∫ g dμ ≤ ∫ g dν + ε (K + ‖g‖)` when `levyProkhorovEDist μ ν < ε`.
* `LevyStochCalc.Probability.abs_integral_sub_integral_le_levyProkhorovDist` — the two-sided
  bound `|∫ g dμ - ∫ g dν| ≤ (K + ‖g‖) · levyProkhorovDist μ ν`.
-/

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace LevyStochCalc.Probability

variable {Ω : Type*} [PseudoMetricSpace Ω]

variable [MeasurableSpace Ω] [OpensMeasurableSpace Ω]

/-- For probability measures `μ`, `ν` on a pseudo-metric space and a nonnegative bounded
continuous `K`-Lipschitz function `g`,
`|∫ g dμ - ∫ g dν| ≤ (K + ‖g‖) · levyProkhorovDist μ ν`. -/
theorem abs_integral_sub_integral_le_levyProkhorovDist {μ ν : Measure Ω}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (g : Ω →ᵇ ℝ) {K : ℝ≥0}
    (hg : LipschitzWith K g) (hg_nn : ∀ x, 0 ≤ g x) :
    |∫ x, g x ∂μ - ∫ x, g x ∂ν| ≤ (K + ‖g‖) * levyProkhorovDist μ ν := by
  set d := levyProkhorovDist μ ν with hd
  have hED : levyProkhorovEDist μ ν = ENNReal.ofReal d := by
    rw [hd, levyProkhorovDist, ENNReal.ofReal_toReal (levyProkhorovEDist_ne_top μ ν)]
  have hd_nn : 0 ≤ d := ENNReal.toReal_nonneg
  have hbound : ∀ ε, d < ε → |∫ x, g x ∂μ - ∫ x, g x ∂ν| ≤ ε * (K + ‖g‖) := by
    intro ε hdε
    have hε : 0 < ε := hd_nn.trans_lt hdε
    have hlt : levyProkhorovEDist μ ν < ENNReal.ofReal ε := by
      rw [hED]; exact (ENNReal.ofReal_lt_ofReal_iff hε).mpr hdε
    have hlt' : levyProkhorovEDist ν μ < ENNReal.ofReal ε := by
      rwa [levyProkhorovEDist_comm]
    have h1 := _root_.Prove2MeSourceProof.h_95e0cc414c3966abf368871c g hg hg_nn hε hlt
    have h2 := _root_.Prove2MeSourceProof.h_95e0cc414c3966abf368871c (μ := ν) (ν := μ) g hg hg_nn hε
      hlt'
    rw [abs_le]
    constructor <;> linarith
  have hlim : Tendsto (fun ε => ε * ((K : ℝ) + ‖g‖)) (𝓝[>] d) (𝓝 (d * (K + ‖g‖))) :=
    ((continuous_id.mul continuous_const).tendsto d).mono_left nhdsWithin_le_nhds
  rw [mul_comm]
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ε hε => hbound ε hε)
end LevyStochCalc.Probability


