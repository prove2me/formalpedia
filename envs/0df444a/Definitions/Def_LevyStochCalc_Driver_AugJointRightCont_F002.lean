-- Prove2me | Definitions.Def_LevyStochCalc_Driver_AugJointRightCont_F002
-- name    : LevyStochCalc_Driver_AugJointRightCont_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:19:14.356163+00:00
-- url     : https://prove2.me/theorems/e6e57b19-21fe-4dc7-b351-abd03314fd73
-- title:
--   Source declarations: LevyStochCalc.Driver.AugJointRightCont
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Driver.AugJointRightCont. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_AugJointRightCont_F001
import Definitions.Def_SourceProof_2e016f6f64c5cb15d61c5cac
import Definitions.Def_SourceProof_cf36e28327ca7caf8bdf4235

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

end LevyStochCalc.Probability

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

namespace LevyDriver

open LevyStochCalc.Probability

variable (D : LevyDriver.{u, v, w} P d ν)

/-- **The germ field of the joint filtration at a nonnegative time is contained in the
augmentation of the filtration there.** -/
theorem filtration_rightCont_le_aug {t : ℝ} (ht : 0 ≤ t) :
    D.filtration.rightCont t ≤ aug (D.filtration t) ‹MeasurableSpace Ω› P := by
  have hle : D.filtration.rightCont t ≤ D.filtration (t + 1) := by
    rw [Filtration.rightCont_eq_of_neBot_nhdsGT D.filtration t]
    exact iInf₂_le (t + 1) (by linarith)
  refine _root_.Prove2MeSourceProof.h_cf36e28327ca7caf8bdf4235 (D.filtration.le t) (D.futureSigma_le t (t + 1))
    (D.filtration.le_rightCont t) (hle.trans (D.filtration_le_sup_futureSigma (by linarith)))
    ((_root_.Prove2MeSourceProof.h_2e016f6f64c5cb15d61c5cac D) ht (by linarith)).symm
/-- **The germ field of the augmented joint filtration at a nonnegative time is its field
there.** -/
theorem rightCont_augFiltration_le_self {t : ℝ} (ht : 0 ≤ t) :
    (Brownian.augFiltration D.filtration P).rightCont t
      ≤ Brownian.augFiltration D.filtration P t := by
  have hseq : ∀ n : ℕ, t < t + ((n : ℝ) + 1)⁻¹ := by
    intro n
    have hpos : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
    linarith
  have hanti : Antitone fun n : ℕ => D.filtration (t + ((n : ℝ) + 1)⁻¹) := by
    intro a b hab
    refine D.filtration.mono ?_
    have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    have hinv : ((b : ℝ) + 1)⁻¹ ≤ ((a : ℝ) + 1)⁻¹ := by gcongr
    linarith
  have h1 : (Brownian.augFiltration D.filtration P).rightCont t
      ≤ ⨅ n : ℕ, aug (D.filtration (t + ((n : ℝ) + 1)⁻¹)) ‹MeasurableSpace Ω› P := by
    refine le_iInf fun n => ?_
    have h2 : (Brownian.augFiltration D.filtration P).rightCont t
        ≤ Brownian.augFiltration D.filtration P (t + ((n : ℝ) + 1)⁻¹) := by
      rw [Filtration.rightCont_eq]
      exact iInf₂_le _ (hseq n)
    have h3 : Brownian.augFiltration D.filtration P (t + ((n : ℝ) + 1)⁻¹)
        = aug (D.filtration (t + ((n : ℝ) + 1)⁻¹)) ‹MeasurableSpace Ω› P := by
      change aug (D.filtration (max (t + ((n : ℝ) + 1)⁻¹) 0)) ‹MeasurableSpace Ω› P = _
      rw [max_eq_left (by linarith [hseq n])]
    rwa [h3] at h2
  rw [_root_.Prove2MeSourceProof.h_67317a800b1937235d5651f7 hanti] at h1
  have h4 : (⨅ n : ℕ, D.filtration (t + ((n : ℝ) + 1)⁻¹)) ≤ D.filtration.rightCont t := by
    rw [Filtration.rightCont_eq]
    refine le_iInf₂ fun u hu => ?_
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < u - t by linarith)
    refine le_trans (iInf_le _ n) (D.filtration.mono ?_)
    rw [one_div] at hn
    linarith
  have h5 : Brownian.augFiltration D.filtration P t
      = aug (D.filtration t) ‹MeasurableSpace Ω› P := by
    change aug (D.filtration (max t 0)) ‹MeasurableSpace Ω› P = _
    rw [max_eq_left ht]
  rw [h5]
  exact h1.trans ((aug_mono h4).trans (aug_le_of_le_aug (D.filtration_rightCont_le_aug ht)))
/-- The germ field of the augmented joint filtration at a nonnegative time equals its field
there. -/
theorem rightCont_augFiltration_eq {t : ℝ} (ht : 0 ≤ t) :
    (Brownian.augFiltration D.filtration P).rightCont t
      = Brownian.augFiltration D.filtration P t :=
  le_antisymm (D.rightCont_augFiltration_le_self ht)
    (Filtration.le_rightCont (Brownian.augFiltration D.filtration P) t)
/-- **The augmented joint filtration of a Lévy driver is right-continuous.** -/
instance isRightContinuous_augFiltration :
    Filtration.IsRightContinuous (Brownian.augFiltration D.filtration P) := by
  constructor
  intro t
  rcases le_or_gt 0 t with ht | ht
  · exact D.rightCont_augFiltration_le_self ht
  · have h1 : (Brownian.augFiltration D.filtration P).rightCont t
        ≤ Brownian.augFiltration D.filtration P (t / 2) := by
      rw [Filtration.rightCont_eq]
      exact iInf₂_le _ (by linarith)
    rw [Brownian.augFiltration_of_nonpos _ _ (by linarith : t / 2 ≤ 0)] at h1
    rw [Brownian.augFiltration_of_nonpos _ _ ht.le]
    exact h1
end LevyDriver

end LevyStochCalc.Driver


