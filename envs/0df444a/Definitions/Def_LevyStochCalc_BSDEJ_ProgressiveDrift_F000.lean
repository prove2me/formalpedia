-- Prove2me | Definitions.Def_LevyStochCalc_BSDEJ_ProgressiveDrift_F000
-- name    : LevyStochCalc_BSDEJ_ProgressiveDrift_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:17:17.039271+00:00
-- url     : https://prove2.me/theorems/2bafe3b3-1a64-4d37-bb3b-18a7ef36c09a
-- title:
--   Source declarations: LevyStochCalc.BSDEJ.ProgressiveDrift
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.BSDEJ.ProgressiveDrift. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_DriftLeg_F001
import Definitions.Def_LevyStochCalc_BSDEJ_DriftLeg_F002
import Definitions.Def_LevyStochCalc_BSDEJ_DriftModification_F001
import Definitions.Def_LevyStochCalc_Ito_JumpDiffusionAdapted_F000
import Definitions.Def_SourceProof_846c5a27154f5e7706e6988e
import Definitions.Def_SourceProof_cf0436ca36261036186bd5e0

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# A progressive modification of a drift with an adapted primitive

Let `φ : Ω → ℝ → ℝ` be jointly measurable, of finite energy on `[0, T]` and vanishing off it, and
suppose that for every `t ∈ [0, T]` the primitive `ω ↦ ∫_0^t φ_s(ω) ds` agrees almost surely with
a function measurable for the right-continuous filtration `ℱ_{t+}`. If `ℱ_0` contains the `P`-null
sets, then `φ` has a modification `φ̃` that is progressively measurable for `ℱ` itself and agrees
with `φ` almost everywhere for `P ⊗ ds` on `Ω × [0, T]`. The hypothesis bears on the primitive
of `φ`, where `exists_progressive_modification_of_rightCont` asks `φ` itself to be progressive for
the right-continuous filtration.

Cut `φ` and its primitive to the `ℱ_0`-measurable, `P`-conull set of sample points with an
integrable path. The cut primitive `A_t = ∫_0^t φ_s ds` (the drift leg) is then
`ℱ_{t+}`-measurable at every time and has continuous paths, so the difference quotient
`c⁻¹ (A_{s − c} − A_{s − 2c})` — the mean of the cut drift over the window `[s − 2c, s − c]` —
reads `A` only at times strictly before `s` and is `ℱ`-progressive. The modification `φ̃` is the
`limsup` of these means as `c ↓ 0`, cut to `[0, T]`, and Lebesgue's differentiation theorem
identifies it with `φ` at almost every time of almost every path.

## Main statements

* `stronglyMeasurable_driftLeg_of_aestronglyMeasurable`: the drift leg is measurable for the
  right-continuous filtration at every time.
* `leftAverage_indicator_eq`: the window mean of the cut drift is a difference quotient of the
  drift leg.
* `progressivelyMeasurable_leftAverage_indicator`: the window means of the cut drift are
  `ℱ`-progressive.
* `exists_progressive_modification_of_adapted_integral`: the progressive modification.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.BSDEJ.Generator

open LevyStochCalc.BSDEJ.Solves

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
  {φ : Ω → ℝ → ℝ} {T : ℝ}

/-- A path that is integrable on `[0, T]` and vanishes off it is integrable on the line. -/
private theorem integrable_of_mem_integrablePaths
    (hφz : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → φ ω s = 0) {ω : Ω}
    (hω : ω ∈ integrablePaths φ T) : Integrable (φ ω) volume := by
  have hind : Integrable ((Set.Icc (0 : ℝ) T).indicator (φ ω)) volume :=
    (integrable_indicator_iff measurableSet_Icc).mpr hω
  refine hind.congr (Eventually.of_forall fun s => ?_)
  by_cases hs : s ∈ Set.Icc (0 : ℝ) T
  · rw [Set.indicator_of_mem hs]
  · rw [Set.indicator_of_notMem hs, hφz ω s hs]
/-- The primitive of a drift vanishing off `[0, T]` is constant after the horizon. -/
private theorem setIntegral_Icc_min (hφz : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → φ ω s = 0)
    (ω : Ω) (r : ℝ) :
    ∫ s in Set.Icc (0 : ℝ) r, φ ω s = ∫ s in Set.Icc (0 : ℝ) (min r T), φ ω s :=
  setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc
    (Set.Icc_subset_Icc le_rfl (min_le_left r T)) fun s hs =>
      hφz ω s fun hsT => hs.2 ⟨hsT.1, le_min hs.1.2 hsT.2⟩
/-- **The drift leg is adapted to the right-continuous filtration.** If the primitive
`ω ↦ ∫_0^t φ_s(ω) ds` is almost surely equal to an `ℱ_{t+}`-measurable function at every
`t ∈ [0, T]` and `ℱ_0` contains the `P`-null sets, then the drift leg of `φ` at every time `r` is
`ℱ_{r+}`-measurable. -/
theorem stronglyMeasurable_driftLeg_of_aestronglyMeasurable
    (hφm : Measurable (Function.uncurry φ)) (hφz : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → φ ω s = 0)
    (hφq : Brownian.Ito.energy P T φ ≠ ⊤)
    (hA : ∀ t ∈ Set.Icc (0 : ℝ) T,
      AEStronglyMeasurable[ℱ.rightCont t] (fun ω => ∫ s in Set.Icc (0 : ℝ) t, φ ω s) P)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 ≤ T)
    (r : ℝ) : StronglyMeasurable[ℱ.rightCont r] (driftLeg φ T r) := by
  rcases lt_or_ge r 0 with hr | hr
  · have heq : driftLeg φ T r = fun _ => (0 : ℝ) := by
      funext ω
      by_cases hω : ω ∈ integrablePaths φ T
      · rw [driftLeg_of_mem hω r, Set.Icc_eq_empty (not_le.mpr hr), setIntegral_empty]
      · exact driftLeg_of_notMem hω r
    rw [heq]
    exact stronglyMeasurable_const
  have hmem : min r T ∈ Set.Icc (0 : ℝ) T := ⟨le_min hr hT, min_le_right r T⟩
  have hg := hA (min r T) hmem
  have hnull' : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ.rightCont r] s :=
    fun s hs h0 => ℱ.le_rightCont r _ (ℱ.mono hr _ (hnull s hs h0))
  have hf : Measurable (driftLeg φ T r) :=
    (_root_.Prove2MeSourceProof.h_846c5a27154f5e7706e6988e hφm).comp (measurable_const.prodMk measurable_id)
  have hgm : Measurable[ℱ.rightCont r] hg.mk :=
    (hg.stronglyMeasurable_mk.mono (ℱ.rightCont.mono (min_le_left r T))).measurable
  refine (_root_.Prove2MeSourceProof.h_7b7fe4c6b4bf6f12571973df hnull' hf hgm ?_).stronglyMeasurable
  filter_upwards [driftLeg_ae_eq hφm hφq r, hg.ae_eq_mk] with ω h1 h2
  rw [h1, setIntegral_Icc_min hφz ω r]
  exact h2
/-- The mean over the window `[s − 2c, s − c]` of a drift cut to the sample points with an
integrable path is the difference quotient `c⁻¹ (A_{s − c} − A_{s − 2c})` of its drift leg. -/
theorem leftAverage_indicator_eq (hφz : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → φ ω s = 0) {c : ℝ}
    (hc : 0 ≤ c) (ω : Ω) (s : ℝ) :
    leftAverage ((integrablePaths φ T).indicator φ) c ω s
      = c⁻¹ * (driftLeg φ T (s - c) ω - driftLeg φ T (s - 2 * c) ω) := by
  unfold leftAverage
  by_cases hω : ω ∈ integrablePaths φ T
  · have hint := integrable_of_mem_integrablePaths hφz hω
    rw [Set.indicator_of_mem hω, driftLeg_of_mem hω, driftLeg_of_mem hω,
      setIntegral_Icc_eq_intervalIntegral hφz, setIntegral_Icc_eq_intervalIntegral hφz,
      intervalIntegral.integral_interval_sub_left (hint.intervalIntegrable)
        (hint.intervalIntegrable), intervalIntegral.integral_of_le (by linarith),
      integral_Icc_eq_integral_Ioc]
  · rw [Set.indicator_of_notMem hω, driftLeg_of_notMem hω, driftLeg_of_notMem hω]
    simp
/-- **The window means of the cut drift are progressive.** Under the hypotheses of
`stronglyMeasurable_driftLeg_of_aestronglyMeasurable`, for every `c > 0` the mean over the
window `[s − 2c, s − c]` of the drift cut to the sample points with an integrable path is
progressively measurable for `ℱ`. -/
theorem progressivelyMeasurable_leftAverage_indicator (hφm : Measurable (Function.uncurry φ))
    (hφz : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → φ ω s = 0) (hφq : Brownian.Ito.energy P T φ ≠ ⊤)
    (hA : ∀ t ∈ Set.Icc (0 : ℝ) T,
      AEStronglyMeasurable[ℱ.rightCont t] (fun ω => ∫ s in Set.Icc (0 : ℝ) t, φ ω s) P)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 ≤ T)
    {c : ℝ} (hc : 0 < c) :
    Probability.ProgressivelyMeasurable ℱ (leftAverage ((integrablePaths φ T).indicator φ) c) := by
  intro t
  set K : ℝ → Ω → ℝ := fun s ω =>
    c⁻¹ * (driftLeg φ T (min s t - c) ω - driftLeg φ T (min s t - 2 * c) ω) with hK
  have hleg : ∀ {a : ℝ}, 0 < a → ∀ s : ℝ, StronglyMeasurable[ℱ t] (driftLeg φ T (min s t - a)) := by
    intro a ha s
    refine (stronglyMeasurable_driftLeg_of_aestronglyMeasurable hφm hφz hφq hA hnull hT
      (min s t - a)).mono ?_
    rw [Filtration.rightCont_eq]
    exact iInf₂_le t (by linarith [min_le_right s t])
  have hKm : ∀ s, StronglyMeasurable[ℱ t] (K s) := fun s =>
    stronglyMeasurable_const.mul ((hleg hc s).sub (hleg (by linarith) s))
  have hKc : ∀ ω, Continuous fun s => K s ω := fun ω =>
    continuous_const.mul
      (((_root_.Prove2MeSourceProof.h_cf0436ca36261036186bd5e0 hφz ω).comp ((continuous_id.min continuous_const).sub
        continuous_const)).sub ((_root_.Prove2MeSourceProof.h_cf0436ca36261036186bd5e0 hφz ω).comp
          ((continuous_id.min continuous_const).sub continuous_const)))
  have hkey : (fun p : Ω × ℝ =>
        (Set.Iic t).indicator (leftAverage ((integrablePaths φ T).indicator φ) c p.1) p.2)
      = {p : Ω × ℝ | p.2 ∈ Set.Iic t}.indicator fun p => K p.2 p.1 := by
    funext p
    by_cases hp : p.2 ∈ Set.Iic t
    · have hp' : p ∈ {p : Ω × ℝ | p.2 ∈ Set.Iic t} := hp
      rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp', leftAverage_indicator_eq hφz hc.le,
        hK]
      dsimp only
      rw [min_eq_left (Set.mem_Iic.mp hp)]
    · have hp' : p ∉ {p : Ω × ℝ | p.2 ∈ Set.Iic t} := hp
      rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp']
  rw [hkey]
  letI : MeasurableSpace Ω := ℱ t
  have hmeas : Measurable fun p : Ω × ℝ => K p.2 p.1 :=
    (measurable_uncurry_of_continuous_of_measurable hKc fun s => (hKm s).measurable).comp
      measurable_swap
  exact (hmeas.indicator (measurable_snd measurableSet_Iic)).stronglyMeasurable
end LevyStochCalc.BSDEJ.Generator


