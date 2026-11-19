-- Prove2me | Definitions.Def_LevyStochCalc_Probability_LevyProkhorovLipschitz_F000
-- name    : LevyStochCalc_Probability_LevyProkhorovLipschitz_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:05:51.354997+00:00
-- url     : https://prove2.me/theorems/f98c1425-430d-43c0-8ca9-eb27fd03be8b
-- title:
--   Source declarations: LevyStochCalc.Probability.LevyProkhorovLipschitz
-- statement:
--   Source-preserving Lean declaration bundle from LevyStochCalc.Probability.LevyProkhorovLipschitz, retaining definitions, helper results, proofs and elaboration context where present.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

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

/-- The `ε`-thickening of a superlevel set `{t ≤ f}` of a `K`-Lipschitz real function lies in the
superlevel set `{t - K ε ≤ f}`. -/
theorem thickening_setOf_le_subset {f : Ω → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (ε t : ℝ) :
    Metric.thickening ε {a | t ≤ f a} ⊆ {a | t - K * ε ≤ f a} := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := Metric.mem_thickening_iff.mp hx
  simp only [mem_setOf_eq] at hy ⊢
  have h0 := hf.dist_le_mul x y
  rw [Real.dist_eq] at h0
  have h1 := neg_abs_le (f x - f y)
  have h2 : (K : ℝ) * dist x y ≤ K * ε := mul_le_mul_of_nonneg_left hxy.le K.coe_nonneg
  linarith
variable [MeasurableSpace Ω] [OpensMeasurableSpace Ω]

end LevyStochCalc.Probability


