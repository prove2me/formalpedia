-- Prove2me | Definitions.Def_SourceProof_fd00f88d1f6410d0b5c23269
-- name    : SourceProof_fd00f88d1f6410d0b5c23269
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T07:13:47.975185+00:00
-- url     : https://prove2.me/theorems/cfabbc98-d808-4881-b1d1-84c591178326
-- title:
--   LevyStochCalc source module: SourceProof_fd00f88d1f6410d0b5c23269
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.rightCont_augFiltration_le` comes from the `LevyStochCalc.Brownian.AugmentedFiltration` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_AugmentedFiltration_F000
import Definitions.Def_SourceProof_3d27237b32316a1fa19a9df4
import Definitions.Def_SourceProof_67317a800b1937235d5651f7

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

end LevyStochCalc.Probability

namespace LevyStochCalc.Brownian

open LevyStochCalc.Probability

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]


theorem _root_.Prove2MeSourceProof.h_fd00f88d1f6410d0b5c23269 (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (μ : Measure Ω) :
    (augFiltration ℱ.rightCont μ).rightCont ≤ augFiltration ℱ.rightCont μ := by
  intro t
  rcases lt_or_ge t 0 with ht | ht
  · have hs : t < t / 2 := by linarith
    have h1 : (LevyStochCalc.Brownian.augFiltration ℱ.rightCont μ).rightCont t
        ≤ LevyStochCalc.Brownian.augFiltration ℱ.rightCont μ (t / 2) := by
      rw [Filtration.rightCont_eq]
      exact iInf₂_le _ hs
    rw [LevyStochCalc.Brownian.augFiltration_of_nonpos _ _ (by linarith : t / 2 ≤ 0)] at h1
    rw [LevyStochCalc.Brownian.augFiltration_of_nonpos _ _ ht.le]
    exact h1
  · have hseq : ∀ n : ℕ, t < t + ((n : ℝ) + 1)⁻¹ := by
      intro n
      have : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
      linarith
    have hanti : Antitone fun n : ℕ => ℱ.rightCont (t + ((n : ℝ) + 1)⁻¹) := by
      intro a b hab
      refine ℱ.rightCont.mono ?_
      have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
      have hinv : ((b : ℝ) + 1)⁻¹ ≤ ((a : ℝ) + 1)⁻¹ := by gcongr
      linarith
    have h1 : (LevyStochCalc.Brownian.augFiltration ℱ.rightCont μ).rightCont t
        ≤ ⨅ n : ℕ, LevyStochCalc.Probability.aug (ℱ.rightCont (t + ((n : ℝ) + 1)⁻¹)) ‹MeasurableSpace Ω› μ := by
      refine le_iInf fun n => ?_
      have h2 : (LevyStochCalc.Brownian.augFiltration ℱ.rightCont μ).rightCont t
          ≤ LevyStochCalc.Brownian.augFiltration ℱ.rightCont μ (t + ((n : ℝ) + 1)⁻¹) := by
        rw [Filtration.rightCont_eq]
        exact iInf₂_le _ (hseq n)
      have h3 : LevyStochCalc.Brownian.augFiltration ℱ.rightCont μ (t + ((n : ℝ) + 1)⁻¹)
          = LevyStochCalc.Probability.aug (ℱ.rightCont (t + ((n : ℝ) + 1)⁻¹)) ‹MeasurableSpace Ω› μ := by
        change LevyStochCalc.Probability.aug (ℱ.rightCont (max (t + ((n : ℝ) + 1)⁻¹) 0)) ‹MeasurableSpace Ω› μ = _
        rw [max_eq_left (by linarith [hseq n])]
      rwa [h3] at h2
    rw [_root_.Prove2MeSourceProof.h_67317a800b1937235d5651f7 hanti] at h1
    have h4 : (⨅ n : ℕ, ℱ.rightCont (t + ((n : ℝ) + 1)⁻¹)) ≤ ℱ.rightCont t := by
      rw [Filtration.rightCont_eq]
      refine le_iInf₂ fun u hu => ?_
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < u - t by linarith)
      refine le_trans (iInf_le _ n) ?_
      rw [Filtration.rightCont_eq]
      refine iInf₂_le u ?_
      rw [one_div] at hn
      linarith
    have h5 : LevyStochCalc.Brownian.augFiltration ℱ.rightCont μ t = LevyStochCalc.Probability.aug (ℱ.rightCont t) ‹MeasurableSpace Ω› μ := by
      change LevyStochCalc.Probability.aug (ℱ.rightCont (max t 0)) ‹MeasurableSpace Ω› μ = _
      rw [max_eq_left ht]
    rw [h5]
    exact le_trans h1 (LevyStochCalc.Probability.aug_mono h4)
end LevyStochCalc.Brownian


