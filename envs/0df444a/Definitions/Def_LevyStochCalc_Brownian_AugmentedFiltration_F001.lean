-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_AugmentedFiltration_F001
-- name    : LevyStochCalc_Brownian_AugmentedFiltration_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T07:14:34.287972+00:00
-- url     : https://prove2.me/theorems/30e2cd25-4a5a-4547-88e9-43b16327ece3
-- title:
--   Source declarations: LevyStochCalc.Brownian.AugmentedFiltration
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.AugmentedFiltration. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_AugmentedFiltration_F000
import Definitions.Def_SourceProof_3d27237b32316a1fa19a9df4
import Definitions.Def_SourceProof_fd00f88d1f6410d0b5c23269

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

instance isRightContinuous_augFiltration (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (μ : Measure Ω) :
    Filtration.IsRightContinuous (augFiltration ℱ.rightCont μ) :=
  ⟨_root_.Prove2MeSourceProof.h_fd00f88d1f6410d0b5c23269 ℱ μ⟩
/-- The `hℱ0` hypothesis, discharged for the augmentation of a right-continuous filtration. -/
theorem hF0_augFiltration (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (μ : Measure Ω) (t : ℝ)
    (ht : t ≤ 0) :
    (augFiltration ℱ.rightCont μ).rightCont 0 ≤ (augFiltration ℱ.rightCont μ).rightCont t := by
  rw [Filtration.IsRightContinuous.eq (𝓕 := augFiltration ℱ.rightCont μ)]
  rw [augFiltration_of_nonpos _ _ ht, augFiltration_of_nonpos _ _ (le_refl (0 : ℝ))]
end LevyStochCalc.Brownian


