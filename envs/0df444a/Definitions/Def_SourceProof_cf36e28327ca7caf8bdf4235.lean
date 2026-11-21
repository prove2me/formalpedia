-- Prove2me | Definitions.Def_SourceProof_cf36e28327ca7caf8bdf4235
-- name    : SourceProof_cf36e28327ca7caf8bdf4235
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:15:23.795924+00:00
-- url     : https://prove2.me/theorems/b59c7d74-a5b9-4982-800f-87131e808d41
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Probability.le_aug_of_indep_of_le_sup
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_AugJointRightCont_F000

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


theorem _root_.Prove2MeSourceProof.h_cf36e28327ca7caf8bdf4235 {𝒜 𝒢 𝒞 : MeasurableSpace Ω} (h𝒜 : 𝒜 ≤ mΩ) (h𝒢 : 𝒢 ≤ mΩ)
    (h𝒜𝒞 : 𝒜 ≤ 𝒞) (h𝒞 : 𝒞 ≤ 𝒜 ⊔ 𝒢) (hind : Indep 𝒞 𝒢 P) :
    𝒞 ≤ aug 𝒜 mΩ P := by
  haveI : IsFiniteMeasure (P.trim h𝒜) := isFiniteMeasure_trim h𝒜
  have hsup : 𝒜 ⊔ 𝒢 ≤ mΩ := sup_le h𝒜 h𝒢
  have h𝒞0 : 𝒞 ≤ mΩ := h𝒞.trans hsup
  have hind𝒜 : Indep 𝒜 𝒢 P := indep_of_indep_of_le_left hind h𝒜𝒞
  intro A hA
  have hA0 : MeasurableSet[mΩ] A := h𝒞0 A hA
  have hfm : Measurable[𝒞] (A.indicator (1 : Ω → ℝ)) := measurable_one.indicator hA
  have hfint : Integrable (A.indicator (1 : Ω → ℝ)) P :=
    (integrable_const (1 : ℝ)).indicator hA0
  have hYm : Measurable[𝒜] (P[A.indicator (1 : Ω → ℝ) | 𝒜]) :=
    stronglyMeasurable_condExp.measurable
  have hzero : (A.indicator (1 : Ω → ℝ) - P[A.indicator (1 : Ω → ℝ) | 𝒜]) =ᵐ[P] 0 := by
    refine LevyStochCalc.Probability.ae_eq_zero_of_forall_setIntegral_eq_zero_isPiSystem hsup
      LevyStochCalc.Probability.sup_eq_generateFrom_interSets LevyStochCalc.Probability.isPiSystem_interSets
      (hfint.sub integrable_condExp) ?_ ?_ ?_
    · exact (stronglyMeasurable_one.indicator (h𝒞 A hA)).sub
        (stronglyMeasurable_condExp.mono le_sup_left)
    · simp only [Pi.sub_apply]
      rw [integral_sub hfint integrable_condExp, integral_condExp h𝒜, sub_self]
    · rintro _ ⟨Z, F, hZ, hF, rfl⟩
      simp only [Pi.sub_apply]
      rw [integral_sub hfint.integrableOn integrable_condExp.integrableOn,
        LevyStochCalc.Probability.setIntegral_inter_of_indep h𝒞0 h𝒢 hind hfm (h𝒜𝒞 Z hZ) hF,
        LevyStochCalc.Probability.setIntegral_inter_of_indep h𝒜 h𝒢 hind𝒜 hYm hZ hF,
        setIntegral_condExp h𝒜 hfint hZ, sub_self]
  have hkey : ∀ᵐ x ∂P,
      A.indicator (1 : Ω → ℝ) x = (P[A.indicator (1 : Ω → ℝ) | 𝒜]) x := by
    filter_upwards [hzero] with x hx
    have hx' : A.indicator (1 : Ω → ℝ) x - (P[A.indicator (1 : Ω → ℝ) | 𝒜]) x = 0 := hx
    linarith
  refine ⟨hA0, (P[A.indicator (1 : Ω → ℝ) | 𝒜]) ⁻¹' Set.Ioi (1 / 2 : ℝ),
    hYm measurableSet_Ioi, ?_⟩
  refine measure_mono_null (fun x hx => ?_) (ae_iff.1 hkey)
  rcases Set.mem_symmDiff.1 hx with ⟨hxA, hxB⟩ | ⟨hxB, hxA⟩
  · have hfx : A.indicator (1 : Ω → ℝ) x = 1 := by simp [hxA]
    have hYx : (P[A.indicator (1 : Ω → ℝ) | 𝒜]) x ≤ 1 / 2 := not_lt.1 hxB
    intro hcon
    rw [hfx] at hcon
    linarith
  · have hfx : A.indicator (1 : Ω → ℝ) x = 0 := by simp [hxA]
    have hYx : 1 / 2 < (P[A.indicator (1 : Ω → ℝ) | 𝒜]) x := hxB
    intro hcon
    rw [hfx] at hcon
    linarith
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


