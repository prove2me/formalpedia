-- Prove2me | Definitions.Def_LevyStochCalc_Driver_AugJointRightCont_F000
-- name    : LevyStochCalc_Driver_AugJointRightCont_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:40:28.3742+00:00
-- url     : https://prove2.me/theorems/68244be6-e938-4948-b776-1849eeb399f5
-- title:
--   Source declarations: LevyStochCalc.Driver.AugJointRightCont
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Driver.AugJointRightCont. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_AugJointUsualConditions_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Right-continuity of the augmented joint filtration of a Lévy driver

Write `𝔸 = augFiltration D.filtration P` for the `0`-clamped augmentation of the joint filtration
of a Lévy driver. Its germ field at a time `t ≥ 0` is already its field at `t`.

The driver's data over `(t, T]` measured from `t` — the Brownian increments `W u - W t` for
`u ∈ (t, T]` and the counts on the measurable regions inside `(t, T] × E` — generates the
σ-algebra `futureSigma t T`. Joined with `ℱ t` it contains `ℱ T`, and it is independent of the
germ field `ℱ₊ t`, the independence coming from the data of a grid starting at `t`. A σ-algebra
that contains `ℱ t`, sits inside the join `ℱ t ⊔ futureSigma t T` and is independent of
`futureSigma t T` differs from `ℱ t` only by null sets: the conditional expectation on `ℱ t` of
the indicator of one of its sets is that indicator, because the two integrate alike over the
π-system of intersections generating the join. Hence `ℱ₊ t ≤ aug (ℱ t)`, and since augmentation
commutes with the countable antitone infimum `⨅ n, ℱ (t + (n + 1)⁻¹)` this gives `𝔸₊ t = 𝔸 t`.
Below time `0` the filtration `𝔸` is constant, so `𝔸` is right-continuous.

## Main statements

* `LevyStochCalc.Probability.le_aug_of_indep_of_le_sup` — the σ-algebra criterion for lying in
  an augmentation.
* `LevyStochCalc.Driver.LevyDriver.filtration_le_sup_futureSigma` — `ℱ T ≤ ℱ t ⊔ futureSigma t T`.
* `LevyStochCalc.Driver.LevyDriver.indep_futureSigma_rightCont` — `futureSigma t T` against
  `ℱ₊ t`.
* `LevyStochCalc.Driver.LevyDriver.filtration_rightCont_le_aug` — `ℱ₊ t ≤ aug (ℱ t)`.
* `LevyStochCalc.Driver.LevyDriver.rightCont_augFiltration_le_self` — `𝔸₊ t ≤ 𝔸 t` for `t ≥ 0`.
* `LevyStochCalc.Driver.LevyDriver.rightCont_augFiltration_eq` — `𝔸₊ t = 𝔸 t` for `t ≥ 0`.
* `LevyStochCalc.Driver.LevyDriver.isRightContinuous_augFiltration` — `𝔸` is right-continuous.
-/

open MeasureTheory ProbabilityTheory

namespace LevyStochCalc.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- For a σ-algebra `𝒩` independent of `𝒢`, a function measurable for `𝒩` integrates over the
intersection of `Z ∈ 𝒩` with `F ∈ 𝒢` to its integral over `Z` times the measure of `F`. -/
theorem setIntegral_inter_of_indep {𝒩 𝒢 : MeasurableSpace Ω} (h𝒩 : 𝒩 ≤ mΩ) (h𝒢 : 𝒢 ≤ mΩ)
    (hind : Indep 𝒩 𝒢 P) {g : Ω → ℝ} (hgm : Measurable[𝒩] g) {Z F : Set Ω}
    (hZ : MeasurableSet[𝒩] Z) (hF : MeasurableSet[𝒢] F) :
    ∫ x in Z ∩ F, g x ∂P = (∫ x in Z, g x ∂P) * P.real F := by
  have hZ0 : MeasurableSet[mΩ] Z := h𝒩 Z hZ
  have hF0 : MeasurableSet[mΩ] F := h𝒢 F hF
  have hX1 : Measurable[𝒩] (Z.indicator g) := hgm.indicator hZ
  have hX2 : Measurable[𝒢] (F.indicator (1 : Ω → ℝ)) := measurable_one.indicator hF
  have hindf : IndepFun (Z.indicator g) (F.indicator (1 : Ω → ℝ)) P := by
    change Indep (MeasurableSpace.comap _ _) (MeasurableSpace.comap _ _) P
    exact indep_of_indep_of_le_right (indep_of_indep_of_le_left hind hX1.comap_le) hX2.comap_le
  have hprod : Z.indicator g * F.indicator (1 : Ω → ℝ) = (Z ∩ F).indicator g := by
    funext x
    by_cases hz : x ∈ Z <;> by_cases hf : x ∈ F <;> simp [hz, hf]
  have hmul := hindf.integral_mul_eq_mul_integral
    ((hX1.mono h𝒩 le_rfl).aestronglyMeasurable) ((hX2.mono h𝒢 le_rfl).aestronglyMeasurable)
  rw [hprod] at hmul
  rw [← integral_indicator (μ := P) (hZ0.inter hF0), hmul, integral_indicator hZ0,
    integral_indicator_one hF0]
end LevyStochCalc.Probability

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

namespace LevyDriver

open LevyStochCalc.Probability

variable (D : LevyDriver.{u, v, w} P d ν)

end LevyDriver

end LevyStochCalc.Driver


