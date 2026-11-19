-- Prove2me | Definitions.Def_SourceProof_95e0cc414c3966abf368871c
-- name    : SourceProof_95e0cc414c3966abf368871c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:06:44.678286+00:00
-- url     : https://prove2.me/theorems/9e919c8b-5798-4b34-af67-90b9712724af
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Probability.integral_le_integral_add_of_levyProkhorovEDist_lt
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_LevyProkhorovLipschitz_F000

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


theorem _root_.Prove2MeSourceProof.h_95e0cc414c3966abf368871c {μ ν : Measure Ω}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (g : Ω →ᵇ ℝ) {K : ℝ≥0}
    (hg : LipschitzWith K g) (hg_nn : ∀ x, 0 ≤ g x) {ε : ℝ} (hε : 0 < ε)
    (hμν : levyProkhorovEDist μ ν < ENNReal.ofReal ε) :
    ∫ x, g x ∂μ ≤ ∫ x, g x ∂ν + ε * (K + ‖g‖) := by
  set φ : ℝ → ℝ := fun s => ν.real {a | s ≤ g a} with hφ
  have φ_anti : Antitone φ := fun s t hst => measureReal_mono (fun a ha => le_trans hst ha)
  have φ_nn : ∀ s, 0 ≤ φ s := fun s => measureReal_nonneg
  have hgnorm : (0 : ℝ) ≤ ‖g‖ := norm_nonneg g
  have hKε : (0 : ℝ) ≤ K * ε := mul_nonneg K.coe_nonneg hε.le
  have hν_eq : ∫ x, g x ∂ν = ∫ t in Set.Ioc 0 ‖g‖, φ t :=
    BoundedContinuousFunction.integral_eq_integral_meas_le g ν (ae_of_all ν hg_nn)
  have hA := BoundedContinuousFunction.integral_le_of_levyProkhorovEDist_lt μ ν hε hμν g
    (ae_of_all μ hg_nn)
  set ψ : ℝ → ℝ := fun t => ν.real (Metric.thickening ε {a | t ≤ g a}) with hψ
  have ψ_anti : Antitone ψ := fun s t hst => measureReal_mono
    (Metric.thickening_subset_of_subset ε (fun a ha => le_trans hst ha))
  have hpt : ∀ t, ψ t ≤ φ (t - K * ε) := fun t =>
    measureReal_mono (LevyStochCalc.Probability.thickening_setOf_le_subset hg ε t)
  have hB : ∫ t in Set.Ioc 0 ‖g‖, ψ t ≤ ∫ t in Set.Ioc 0 ‖g‖, φ (t - K * ε) := by
    refine setIntegral_mono_on ψ_anti.intervalIntegrable.1 ?_ measurableSet_Ioc
      (fun t _ => hpt t)
    exact (φ_anti.comp_monotone fun a b h => by linarith).intervalIntegrable.1
  have hshift : ∫ t in Set.Ioc 0 ‖g‖, φ (t - K * ε) ≤ K * ε + ∫ x, g x ∂ν := by
    have e1 : ∫ t in Set.Ioc 0 ‖g‖, φ (t - K * ε) = ∫ s in (-(K * ε))..(‖g‖ - K * ε), φ s := by
      rw [← intervalIntegral.integral_of_le hgnorm,
        intervalIntegral.integral_comp_sub_right φ (K * ε), zero_sub]
    have e2 : ∫ s in (-(K * ε))..(‖g‖ - K * ε), φ s
        = (∫ s in (-(K * ε))..(0 : ℝ), φ s) + ∫ s in (0 : ℝ)..(‖g‖ - K * ε), φ s :=
      (intervalIntegral.integral_add_adjacent_intervals
        φ_anti.intervalIntegrable φ_anti.intervalIntegrable).symm
    have hneg : ∫ s in (-(K * ε))..(0 : ℝ), φ s = K * ε := by
      have hone : Set.EqOn φ (fun _ => (1 : ℝ)) (Set.uIcc (-(K * ε)) 0) := by
        intro s hs
        rw [Set.uIcc_of_le (by linarith : -((K : ℝ) * ε) ≤ 0)] at hs
        have huniv : {a | s ≤ g a} = Set.univ :=
          Set.eq_univ_of_forall fun a => le_trans hs.2 (hg_nn a)
        simp only [hφ, huniv, probReal_univ]
      rw [intervalIntegral.integral_congr hone, intervalIntegral.integral_const, smul_eq_mul,
        mul_one]
      ring
    have hpos : ∫ s in (0 : ℝ)..(‖g‖ - K * ε), φ s ≤ ∫ x, g x ∂ν := by
      have e3 : ∫ s in (0 : ℝ)..‖g‖, φ s
          = (∫ s in (0 : ℝ)..(‖g‖ - K * ε), φ s) + ∫ s in (‖g‖ - K * ε)..‖g‖, φ s :=
        (intervalIntegral.integral_add_adjacent_intervals
          φ_anti.intervalIntegrable φ_anti.intervalIntegrable).symm
      rw [hν_eq, ← intervalIntegral.integral_of_le hgnorm, e3]
      exact le_add_of_nonneg_right
        (intervalIntegral.integral_nonneg (by linarith) fun s _ => φ_nn s)
    rw [e1, e2, hneg]
    linarith
  rw [hψ] at hA
  linarith [hA, hB, hshift]
end LevyStochCalc.Probability


