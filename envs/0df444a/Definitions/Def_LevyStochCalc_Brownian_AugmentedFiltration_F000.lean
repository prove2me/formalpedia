-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_AugmentedFiltration_F000
-- name    : LevyStochCalc_Brownian_AugmentedFiltration_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T21:58:22.506031+00:00
-- url     : https://prove2.me/theorems/d5937b8d-dde8-4d81-99d5-112a70fa87ce
-- title:
--   Source declarations: LevyStochCalc.Brownian.AugmentedFiltration
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.AugmentedFiltration. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_Filtered_F001
import Definitions.Def_LevyStochCalc_Brownian_Filtered_F002
import Definitions.Def_LevyStochCalc_Probability_Augmentation_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The augmented Brownian filtration

`augFiltration ℱ μ` freezes `ℱ` before time `0` and adds to each `ℱ t` the measurable sets that
differ from a set of `ℱ t` by a `μ`-null set. A Brownian motion `W` for `ℱ` stays one for
`augFiltration ℱ P`: adaptedness only grows, and independence survives because an augmented set
differs from a set of the original σ-algebra by a null set. The result is constant before time
`0` and its time-`0` σ-algebra contains every measurable null set, which is what a continuous
adapted version of an Itô process needs. Augmentation adds null sets only and does not make a
filtration right-continuous; the augmentation of the right-continuation `ℱ₊` is right-continuous,
and so, by a separate argument, is the augmentation of the joint filtration of a Lévy driver
(`LevyStochCalc.Driver.LevyDriver.isRightContinuous_augFiltration`).

## Main statements

* `LevyStochCalc.Probability.indep_aug` — independence survives augmentation.
* `LevyStochCalc.Brownian.augFiltration` — the `0`-clamped augmented filtration.
* `LevyStochCalc.Brownian.isBrownianFiltration_augFiltration` — it is a Brownian filtration.
* `LevyStochCalc.Brownian.isRightContinuous_augFiltration` — the augmentation of `ℱ₊` is
  right-continuous.
-/

open MeasureTheory ProbabilityTheory

namespace LevyStochCalc.Probability

/-- **Independence survives augmentation by the null sets.** -/
theorem indep_aug {Ω : Type*} {mΩ m 𝒩 : MeasurableSpace Ω} (μ : @Measure Ω mΩ)
    (h : @Indep Ω m 𝒩 mΩ μ) : @Indep Ω (aug m mΩ μ) 𝒩 mΩ μ := by
  rw [Indep_iff] at h ⊢
  rintro A C ⟨-, B, hB, hAB⟩ hC
  have hae : A =ᵐ[μ] B := MeasureTheory.measure_symmDiff_eq_zero_iff.mp hAB
  have h1 : μ A = μ B := MeasureTheory.measure_congr hae
  have h2 : μ (A ∩ C) = μ (B ∩ C) :=
    MeasureTheory.measure_congr (hae.inter (Filter.EventuallyEq.refl _ _))
  rw [h1, h2]
  exact h B C hB hC
end LevyStochCalc.Probability

namespace LevyStochCalc.Brownian

open LevyStochCalc.Probability

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The filtration obtained by freezing `ℱ` before time `0` and augmenting each σ-algebra by
the `μ`-null sets. -/
def augFiltration (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (μ : Measure Ω) :
    Filtration ℝ ‹MeasurableSpace Ω› where
  seq t := aug (ℱ (max t 0)) ‹MeasurableSpace Ω› μ
  mono' _ _ hst := aug_mono (ℱ.mono (max_le_max hst le_rfl))
  le' _ := aug_le
theorem le_augFiltration (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (μ : Measure Ω) (t : ℝ) :
    ℱ t ≤ augFiltration ℱ μ t :=
  le_trans (ℱ.mono (le_max_left t 0)) (le_aug (ℱ.le _))
theorem augFiltration_of_nonpos (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (μ : Measure Ω)
    {t : ℝ} (ht : t ≤ 0) : augFiltration ℱ μ t = augFiltration ℱ μ 0 := by
  change aug (ℱ (max t 0)) ‹MeasurableSpace Ω› μ = aug (ℱ (max 0 0)) ‹MeasurableSpace Ω› μ
  rw [max_eq_right ht, max_self]
theorem measurableSet_augFiltration_of_null (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (μ : Measure Ω) {s : Set Ω} (hs : MeasurableSet s) (h0 : μ s = 0) :
    MeasurableSet[augFiltration ℱ μ 0] s :=
  measurableSet_aug_of_null hs h0
/-- **The `0`-clamped augmented filtration is a Brownian filtration.** -/
theorem isBrownianFiltration_augFiltration {W : BrownianMotion P}
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (h : IsBrownianFiltration W ℱ) :
    IsBrownianFiltration W (augFiltration ℱ P) where
  measurable t := fun A hA => le_augFiltration ℱ P t _ (h.measurable t hA)
  indep_future s hs := by
    have hfeq : (augFiltration ℱ P) s = aug (ℱ s) ‹MeasurableSpace Ω› P := by
      change aug (ℱ (max s 0)) ‹MeasurableSpace Ω› P = aug (ℱ s) ‹MeasurableSpace Ω› P
      rw [max_eq_left hs]
    rw [hfeq]
    exact indep_aug P (h.indep_future hs)
end LevyStochCalc.Brownian


