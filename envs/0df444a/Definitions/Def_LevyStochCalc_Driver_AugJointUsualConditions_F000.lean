-- Prove2me | Definitions.Def_LevyStochCalc_Driver_AugJointUsualConditions_F000
-- name    : LevyStochCalc_Driver_AugJointUsualConditions_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:37:46.809971+00:00
-- url     : https://prove2.me/theorems/2084aa59-66c6-4b76-8f30-eecbd42665e0
-- title:
--   Source declarations: LevyStochCalc.Driver.AugJointUsualConditions
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Driver.AugJointUsualConditions. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_GermIndep_F001
import Definitions.Def_LevyStochCalc_Driver_GermIndep_F002
import Definitions.Def_LevyStochCalc_Driver_JointFiltration_F000
import Definitions.Def_SourceProof_67317a800b1937235d5651f7

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The usual conditions for the augmented joint filtration of a Lévy driver

Write `𝔸 = augFiltration D.filtration P` for the `0`-clamped augmentation of the joint filtration
of a Lévy driver. Its germ field at `0` is already its time-`0` field: augmentation commutes with
the countable antitone infimum `⨅ n, D.filtration (n + 1)⁻¹` (`aug_iInf_of_antitone`), that
infimum is the germ field `D.filtration₊ 0` of the driver, and by Blumenthal's `0`-`1` law every
set of the germ field is null or conull, hence differs from `∅` or from `Set.univ` by a null set
and so already lies in `aug (D.filtration 0)`.

Consequently `𝔸₊ 0 = 𝔸 0`, and `𝔸₊` carries the two hypotheses that the càdlàg-modification
lemmas ask of a filtration: it is constant in the sense `𝔸₊ 0 ≤ 𝔸₊ t` for `t ≤ 0`, and it
contains every null set.

## Main statements

* `LevyStochCalc.Driver.LevyDriver.filtration_rightCont_zero_le_aug` — the germ field of the
  driver sits inside `aug (D.filtration 0)`.
* `LevyStochCalc.Driver.LevyDriver.rightCont_augFiltration_zero_le` — `𝔸₊ 0 ≤ 𝔸 0`.
* `LevyStochCalc.Driver.LevyDriver.rightCont_augFiltration_zero_eq` — `𝔸₊ 0 = 𝔸 0`.
* `LevyStochCalc.Driver.LevyDriver.rightCont_augFiltration_zero_le_rightCont` — `𝔸₊ 0 ≤ 𝔸₊ t`.
* `LevyStochCalc.Driver.LevyDriver.measurableSet_rightCont_augFiltration_of_null` — every null
  set lies in `𝔸₊ 0`.
-/

open MeasureTheory ProbabilityTheory

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

namespace LevyDriver

open LevyStochCalc.Probability

variable (D : LevyDriver.{u, v, w} P d ν)

/-- The germ field of the driver is contained in the augmentation of its time-`0` field: each of
its sets is null or conull, hence differs from `∅` or from `Set.univ` by a null set. -/
theorem filtration_rightCont_zero_le_aug :
    D.filtration.rightCont 0 ≤ aug (D.filtration 0) ‹MeasurableSpace Ω› P := by
  intro A hA
  have hA0 : MeasurableSet A := D.filtration.rightCont.le 0 A hA
  rcases (_root_.Prove2MeSourceProof.h_4056caec4402ab97b0c897e1 D) A hA with h0 | h1
  · exact measurableSet_aug_of_null hA0 h0
  · have hc : P Aᶜ = 0 := by rw [prob_compl_eq_one_sub hA0, h1, tsub_self]
    have hcompl : MeasurableSet[aug (D.filtration 0) ‹MeasurableSpace Ω› P] Aᶜ :=
      measurableSet_aug_of_null hA0.compl hc
    simpa using hcompl.compl
/-- **The germ field of the augmented joint filtration is its time-`0` field.** -/
theorem rightCont_augFiltration_zero_le :
    (Brownian.augFiltration D.filtration P).rightCont 0
      ≤ Brownian.augFiltration D.filtration P 0 := by
  have hpos : ∀ n : ℕ, (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := fun n => by positivity
  have hanti : Antitone fun n : ℕ => D.filtration (((n : ℝ) + 1)⁻¹) := by
    intro a b hab
    refine D.filtration.mono ?_
    have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    gcongr
  have h1 : (Brownian.augFiltration D.filtration P).rightCont 0
      ≤ ⨅ n : ℕ, aug (D.filtration (((n : ℝ) + 1)⁻¹)) ‹MeasurableSpace Ω› P := by
    refine le_iInf fun n => ?_
    have h2 : (Brownian.augFiltration D.filtration P).rightCont 0
        ≤ Brownian.augFiltration D.filtration P (((n : ℝ) + 1)⁻¹) := by
      rw [Filtration.rightCont_eq]
      exact iInf₂_le _ (hpos n)
    have h3 : Brownian.augFiltration D.filtration P (((n : ℝ) + 1)⁻¹)
        = aug (D.filtration (((n : ℝ) + 1)⁻¹)) ‹MeasurableSpace Ω› P := by
      change aug (D.filtration (max (((n : ℝ) + 1)⁻¹) 0)) ‹MeasurableSpace Ω› P = _
      rw [max_eq_left (hpos n).le]
    rwa [h3] at h2
  rw [_root_.Prove2MeSourceProof.h_67317a800b1937235d5651f7 hanti] at h1
  have h4 : (⨅ n : ℕ, D.filtration (((n : ℝ) + 1)⁻¹)) ≤ D.filtration.rightCont 0 := by
    rw [Filtration.rightCont_eq]
    refine le_iInf₂ fun u hu => ?_
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < u from hu)
    refine le_trans (iInf_le _ n) (D.filtration.mono ?_)
    rw [one_div] at hn
    exact hn.le
  have h5 : Brownian.augFiltration D.filtration P 0
      = aug (D.filtration 0) ‹MeasurableSpace Ω› P := by
    change aug (D.filtration (max 0 0)) ‹MeasurableSpace Ω› P = _
    rw [max_self]
  rw [h5]
  exact h1.trans ((aug_mono h4).trans (aug_le_of_le_aug D.filtration_rightCont_zero_le_aug))
/-- The time-`0` field of the augmented joint filtration is contained in its germ field. -/
theorem augFiltration_zero_le_rightCont :
    Brownian.augFiltration D.filtration P 0
      ≤ (Brownian.augFiltration D.filtration P).rightCont 0 :=
  Filtration.le_rightCont _ 0
/-- The germ field of the augmented joint filtration equals its time-`0` field. -/
theorem rightCont_augFiltration_zero_eq :
    (Brownian.augFiltration D.filtration P).rightCont 0
      = Brownian.augFiltration D.filtration P 0 :=
  le_antisymm D.rightCont_augFiltration_zero_le D.augFiltration_zero_le_rightCont
/-- The germ field of the augmented joint filtration at `0` is its smallest field: it is
contained in the germ field at every time, `0`-clamping making `𝔸 0` the minimum of `𝔸`. -/
theorem rightCont_augFiltration_zero_le_rightCont (t : ℝ) :
    (Brownian.augFiltration D.filtration P).rightCont 0
      ≤ (Brownian.augFiltration D.filtration P).rightCont t := by
  rw [D.rightCont_augFiltration_zero_eq, Filtration.rightCont_eq]
  refine le_iInf₂ fun j hj => ?_
  rcases le_or_gt j 0 with hj0 | hj0
  · exact le_of_eq (Brownian.augFiltration_of_nonpos D.filtration P hj0).symm
  · exact (Brownian.augFiltration D.filtration P).mono hj0.le
/-- The right-continuation of the augmented joint filtration is constant before time `0`. -/
theorem hF0_augFiltration_rightCont (t : ℝ) (_ht : t ≤ 0) :
    (Brownian.augFiltration D.filtration P).rightCont 0
      ≤ (Brownian.augFiltration D.filtration P).rightCont t :=
  D.rightCont_augFiltration_zero_le_rightCont t
/-- Every `P`-null set lies in the germ field of the augmented joint filtration. -/
theorem measurableSet_rightCont_augFiltration_of_null (s : Set Ω) (hs : MeasurableSet s)
    (h0 : P s = 0) :
    MeasurableSet[(Brownian.augFiltration D.filtration P).rightCont 0] s :=
  (Filtration.le_rightCont (Brownian.augFiltration D.filtration P) 0) _
    (D.measurableSet_augFiltration_of_null hs h0)
/-- A function measurable for the germ field of the augmented joint filtration is measurable for
its time-`0` field. -/
theorem stronglyMeasurable_augFiltration_zero {β : Type*} [TopologicalSpace β] {X : Ω → β}
    (hX : StronglyMeasurable[(Brownian.augFiltration D.filtration P).rightCont 0] X) :
    StronglyMeasurable[Brownian.augFiltration D.filtration P 0] X :=
  hX.mono D.rightCont_augFiltration_zero_le
end LevyDriver

end LevyStochCalc.Driver


