-- Prove2me | Definitions.Def_NonvacuityInfiniteActivity_F000
-- name    : NonvacuityInfiniteActivity_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:44:48.261787+00:00
-- url     : https://prove2.me/theorems/c98ab5e8-6421-4f5f-9a3b-79bb4c31f6ca
-- title:
--   Source declarations: NonvacuityInfiniteActivity
-- statement:
--   Source-preserving extracted declarations from NonvacuityInfiniteActivity. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_Solves_F000
import Definitions.Def_LevyStochCalc_Brownian_AugmentedFiltration_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedIntegrandComplete_F000
import Definitions.Def_NonvacuityContract_F000
import Definitions.Def_SourceProof_01c878d1e4a6afef88ed0c78
import Definitions.Def_SourceProof_650b7098f620aa4310e44016

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# A Lévy driver whose mark intensity has infinite total mass

Lebesgue measure on the mark space `ℝ` is σ-finite with `volume ℝ = ∞`, so the reference
intensity `volume|_{[0, ∞)} ⊗ volume` gives the time-space window `(0, 1] × ℝ` infinite mass and
the box `(0, 1] × [0, 1]` mass `1`. A Lévy driver with one Brownian coordinate and this mark
intensity therefore has an almost surely infinite count on the window, while on the box the count
has mean `1` and vanishes with probability `exp (-1)`, the Itô–Lévy integral of the mark
indicator `1_{[0,1]}` has second moment `1` on `[0, 1]`, and the backward equation with vanishing
generator, terminal datum `W_1` and horizon `1` is solvable with value process the Brownian value
at the horizon.

## Main statements

* `referenceIntensity_stepRegion_volume` and `referenceIntensity_markBox` — the reference
  intensity of `(0, 1] × ℝ` is `∞` and that of `(0, 1] × [0, 1]` is `1`.
* `count_stepRegion_ae_eq_top` — the count on `(0, 1] × ℝ` is almost surely `∞`.
* `lintegral_count_markBox` and `prob_count_markBox_eq_zero` — the count on `(0, 1] × [0, 1]`
  has mean `1` and vanishes with probability `exp (-1)`, whence `regionSigma_markBox_ne_bot`.
* `lintegral_sq_markWindowIntegral` and `markWindowIntegral_not_ae_zero` — the Itô–Lévy integral
  of the mark indicator `1_{[0,1]}` on `[0, 1]` has second moment `1` and is not almost surely
  `0`.
* `exists_unique_solvesBSDEJ_volume` — existence and uniqueness for the backward equation with
  vanishing generator, terminal datum `W_1` and horizon `1`, with
  `solvesBSDEJ_zero_generator_Y_terminal` and `solvesBSDEJ_zero_generator_Y_not_ae_zero` — the
  value process of any solution agrees at the horizon with `W_1` and is not almost surely `0`.
* `exists_levyDriver_infinite_activity` — the same statements on a probability space delivered
  by the existence theorem for Lévy drivers.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, §2.3, §4.2.
* Delong, *BSDEs with Jumps and their Actuarial and Financial Applications*, Springer 2013,
  §4.1.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Examples.Nonvacuity

open LevyStochCalc.BSDEJ.Solves
open LevyStochCalc.Driver (LevyDriver)

universe u

/-! ### The infinite-activity intensity and its two reference boxes -/

section Intensity

/-- The mark window `[0, 1]`. -/
def markWindow : Set ℝ := Set.Icc (0 : ℝ) 1
/-- The time-space box `(0, 1] × [0, 1]`. -/
def markBox : Set (ℝ × ℝ) := Set.Ioc (0 : ℝ) 1 ×ˢ markWindow
/-- The mark window `[0, 1]` is measurable. -/
theorem measurableSet_markWindow : MeasurableSet markWindow := measurableSet_Icc
/-- The box `(0, 1] × [0, 1]` is measurable. -/
theorem measurableSet_markBox : MeasurableSet markBox :=
  measurableSet_Ioc.prod measurableSet_markWindow
/-- The Lebesgue intensity of the mark window `[0, 1]` is `1`. -/
theorem volume_markWindow : (volume : Measure ℝ) markWindow = 1 := by
  rw [markWindow, Real.volume_Icc]
  simp
/-- The Lebesgue intensity of the mark window `[0, 1]` is finite. -/
theorem volume_markWindow_ne_top : (volume : Measure ℝ) markWindow ≠ ⊤ := by
  rw [volume_markWindow]
  exact ENNReal.one_ne_top
/-- The Lebesgue intensity of the mark window `[0, 1]` is positive. -/
theorem volume_markWindow_pos : 0 < (volume : Measure ℝ) markWindow := by
  rw [volume_markWindow]
  norm_num
/-- The reference intensity of the window `(0, 1] × ℝ` under Lebesgue marks is infinite. -/
theorem referenceIntensity_stepRegion_volume :
    Poisson.referenceIntensity (volume : Measure ℝ) stepRegion = ⊤ := by
  rw [stepRegion, referenceIntensity_box (volume : Measure ℝ) Set.univ 1, Real.volume_univ]
  simp
/-- The reference intensity of the box `(0, 1] × [0, 1]` under Lebesgue marks is `1`. -/
theorem referenceIntensity_markBox :
    Poisson.referenceIntensity (volume : Measure ℝ) markBox = 1 := by
  rw [markBox, referenceIntensity_box (volume : Measure ℝ) markWindow 1, volume_markWindow]
  simp
/-- The reference intensity of the box `(0, 1] × [0, 1]` under Lebesgue marks is finite. -/
theorem referenceIntensity_markBox_ne_top :
    Poisson.referenceIntensity (volume : Measure ℝ) markBox ≠ ⊤ := by
  rw [referenceIntensity_markBox]
  exact ENNReal.one_ne_top
end Intensity

/-! ### The counts on the two boxes -/

section Counts

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- The count of a Poisson random measure with Lebesgue mark intensity on the window
`(0, 1] × ℝ` is almost surely infinite. -/
theorem count_stepRegion_ae_eq_top (N : Poisson.PoissonRandomMeasure P (volume : Measure ℝ)) :
    ∀ᵐ ω ∂P, N.N ω stepRegion = ⊤ :=
  N.infinite_at_infinite_intensity measurableSet_stepRegion referenceIntensity_stepRegion_volume
/-- The mean count of a Poisson random measure with Lebesgue mark intensity on the box
`(0, 1] × [0, 1]` is `1`. -/
theorem lintegral_count_markBox (N : Poisson.PoissonRandomMeasure P (volume : Measure ℝ)) :
    ∫⁻ ω, N.N ω markBox ∂P = 1 := by
  rw [markBox, lintegral_count_box N measurableSet_markWindow volume_markWindow_ne_top 1,
    volume_markWindow]
  simp
/-- The count of a Poisson random measure with Lebesgue mark intensity on the box
`(0, 1] × [0, 1]` is not almost surely `0`. -/
theorem count_markBox_not_ae_zero (N : Poisson.PoissonRandomMeasure P (volume : Measure ℝ)) :
    ¬ ∀ᵐ ω ∂P, N.N ω markBox = 0 :=
  count_not_ae_zero N measurableSet_markWindow volume_markWindow_ne_top volume_markWindow_pos
    zero_lt_one
/-- A Poisson random measure with Lebesgue mark intensity has no point in the box
`(0, 1] × [0, 1]` with probability `exp (-1)`. -/
theorem prob_count_markBox_eq_zero (N : Poisson.PoissonRandomMeasure P (volume : Measure ℝ)) :
    P {ω | N.N ω markBox = 0} = ENNReal.ofReal (Real.exp (-1)) := by
  rw [prob_count_eq_zero N measurableSet_markBox referenceIntensity_markBox_ne_top,
    referenceIntensity_markBox]
  norm_num
/-- The σ-algebra generated by the count of a Lévy driver with Lebesgue mark intensity on the
box `(0, 1] × [0, 1]` is not trivial. -/
theorem regionSigma_markBox_ne_bot (D : LevyDriver P d (volume : Measure ℝ)) :
    D.regionSigma markBox ≠ ⊥ := by
  intro h
  have hS := measurableSet_regionSigma_count_zero D markBox
  rw [h] at hS
  have hP := prob_count_markBox_eq_zero D.N
  rcases MeasurableSpace.measurableSet_bot_iff.mp hS with h0 | h1
  · rw [h0, measure_empty] at hP
    exact ofReal_exp_neg_one_ne_zero hP.symm
  · rw [h1, measure_univ] at hP
    exact ofReal_exp_neg_one_ne_one hP.symm
end Counts

/-! ### The Itô–Lévy integral of the mark indicator -/

section JumpIntegral

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- The Itô–Lévy integral of the mark indicator `1_{[0,1]}` against the compensated Poisson
random measure of a Lévy driver with Lebesgue mark intensity, on the joint filtration. -/
noncomputable def markWindowIntegral (D : LevyDriver P d (volume : Measure ℝ)) : ℝ → Ω → ℝ :=
  Poisson.Compensated.stochasticIntegral D.N D.filtration (_root_.Prove2MeSourceProof.h_98d5b80f0fbd482e08c8d6f3 D)
    (fun _ _ e => markWindow.indicator (fun _ => (1 : ℝ)) e)
    (measurable_indicator_mark measurableSet_markWindow)
    (_root_.Prove2MeSourceProof.h_d5966f17bb5aa768e87c164d D.filtration measurableSet_markWindow)
    (lintegral_sq_indicator_mark_lt_top measurableSet_markWindow volume_markWindow_ne_top)
/-- The Itô–Lévy integral of the mark indicator `1_{[0,1]}` on `[0, 1]` has second moment
`1`. -/
theorem lintegral_sq_markWindowIntegral (D : LevyDriver P d (volume : Measure ℝ)) :
    ∫⁻ ω, (‖markWindowIntegral D 1 ω‖₊ : ℝ≥0∞) ^ 2 ∂P = 1 := by
  rw [markWindowIntegral, lintegral_sq_itoLevyIntegral_indicator D.N D.filtration
      (_root_.Prove2MeSourceProof.h_98d5b80f0fbd482e08c8d6f3 D) measurableSet_markWindow volume_markWindow_ne_top zero_lt_one,
    volume_markWindow]
  simp
/-- The Itô–Lévy integral of the mark indicator `1_{[0,1]}` on `[0, 1]` is not almost surely
`0`. -/
theorem markWindowIntegral_not_ae_zero (D : LevyDriver P d (volume : Measure ℝ)) :
    ¬ markWindowIntegral D 1 =ᵐ[P] fun _ => (0 : ℝ) :=
  _root_.Prove2MeSourceProof.h_041f540df3d22dd188af52e6 D.N D.filtration (_root_.Prove2MeSourceProof.h_98d5b80f0fbd482e08c8d6f3 D)
    measurableSet_markWindow volume_markWindow_ne_top volume_markWindow_pos zero_lt_one
end JumpIntegral

/-! ### The backward equation with vanishing generator -/

section Backward

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The vanishing generator is measurable in `(s, y, z)` at each fixed jump variable. -/
theorem measurable_zero_generator_volume (_u : ℝ → ℝ) :
    Measurable fun _r : ℝ × ℝ × (Fin 1 → ℝ) => (0 : ℝ) := measurable_const
/-- The vanishing generator obeys the `L²(volume)` Lipschitz bound with constant `0`. -/
theorem lipschitz_zero_generator_volume (_s y₁ y₂ : ℝ) (z₁ z₂ : Fin 1 → ℝ) (u₁ u₂ : ℝ → ℝ) :
    (‖(0 : ℝ) - (0 : ℝ)‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal 0 *
      ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
        + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂(volume : Measure ℝ)) ^ (1 / 2 : ℝ)) := by
  simp
/-- The value at time `1` of the Brownian coordinate of a Lévy driver with Lebesgue mark
intensity is strongly measurable for the augmented joint filtration at time `1`. -/
theorem aestronglyMeasurable_brownian_one_volume (D : LevyDriver P 1 (volume : Measure ℝ)) :
    AEStronglyMeasurable[augJoint D 1] (fun ω => (D.W.W 0).W 1 ω) P := by
  have hnat : StronglyMeasurable[Brownian.Martingale.naturalFiltration (D.W.W 0) 1]
      ((D.W.W 0).W 1) :=
    MeasureTheory.Filtration.stronglyAdapted_natural
      (u := (D.W.W 0).W) (fun t => ((D.W.W 0).measurable_eval t).stronglyMeasurable) 1
  have hle : Brownian.Martingale.naturalFiltration (D.W.W 0) 1 ≤ augJoint D 1 :=
    ((D.W.naturalFiltration_coord_le 0 1).trans (D.naturalFiltration_brownian_le 1)).trans
      (Brownian.le_augFiltration D.filtration P 1)
  exact (hnat.mono hle).aestronglyMeasurable
/-- The backward equation with vanishing generator, terminal datum `W_1` and horizon `1` over a
Lévy driver with Lebesgue mark intensity has a solution triple, and any two solution triples
agree almost surely at every time of the horizon in the value process and with vanishing energy
of the difference on the horizon in the diffusion and jump integrands. -/
theorem exists_unique_solvesBSDEJ_volume (D : LevyDriver P 1 (volume : Measure ℝ)) :
    (∃ (Y : ℝ → Ω → ℝ) (Z : ℝ → Ω → (Fin 1 → ℝ)) (U : ℝ → Ω → ℝ → ℝ),
        SolvesBSDEJ D (fun _ _ _ _ => (0 : ℝ)) (fun ω => (D.W.W 0).W 1 ω) 1 Y Z U) ∧
      ∀ (Y₁ Y₂ : ℝ → Ω → ℝ) (Z₁ Z₂ : ℝ → Ω → (Fin 1 → ℝ)) (U₁ U₂ : ℝ → Ω → ℝ → ℝ),
        SolvesBSDEJ D (fun _ _ _ _ => (0 : ℝ)) (fun ω => (D.W.W 0).W 1 ω) 1 Y₁ Z₁ U₁ →
        SolvesBSDEJ D (fun _ _ _ _ => (0 : ℝ)) (fun ω => (D.W.W 0).W 1 ω) 1 Y₂ Z₂ U₂ →
          (∀ t ∈ Set.Icc (0 : ℝ) 1, Y₁ t =ᵐ[P] Y₂ t) ∧
          (∀ j, Brownian.Ito.energy P 1 (fun ω s => Z₁ s ω j - Z₂ s ω j) = 0) ∧
          Poisson.Compensated.markedEnergy P (volume : Measure ℝ) 1
            (fun ω s e => U₁ s ω e - U₂ s ω e) = 0 := by
  have hf0 : ∫⁻ _s in Set.Icc (0 : ℝ) 1, (‖(0 : ℝ)‖₊ : ℝ≥0∞) ^ 2 < ⊤ := by simp
  exact _root_.Prove2MeSourceProof.h_01c878d1e4a6afef88ed0c78 D (fun _ _ _ _ => (0 : ℝ)) (L := 0) le_rfl
    measurable_zero_generator_volume lipschitz_zero_generator_volume zero_lt_one hf0
    (_root_.Prove2MeSourceProof.h_650b7098f620aa4310e44016 (D.W.W 0) 1)
    (aestronglyMeasurable_brownian_one_volume D)
/-- The value process of a solution of the backward equation with vanishing generator, terminal
datum `W_1` and horizon `1` agrees at the horizon with the Brownian value. -/
theorem solvesBSDEJ_zero_generator_Y_terminal {D : LevyDriver P 1 (volume : Measure ℝ)}
    {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin 1 → ℝ)} {U : ℝ → Ω → ℝ → ℝ}
    (h : SolvesBSDEJ D (fun _ _ _ _ => (0 : ℝ)) (fun ω => (D.W.W 0).W 1 ω) 1 Y Z U) :
    Y 1 =ᵐ[P] fun ω => (D.W.W 0).W 1 ω :=
  h.Y_terminal zero_le_one
/-- The value process of a solution of the backward equation with vanishing generator, terminal
datum `W_1` and horizon `1` is not almost surely `0` at the horizon. -/
theorem solvesBSDEJ_zero_generator_Y_not_ae_zero {D : LevyDriver P 1 (volume : Measure ℝ)}
    {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin 1 → ℝ)} {U : ℝ → Ω → ℝ → ℝ}
    (h : SolvesBSDEJ D (fun _ _ _ _ => (0 : ℝ)) (fun ω => (D.W.W 0).W 1 ω) 1 Y Z U) :
    ¬ (Y 1 =ᵐ[P] fun _ => (0 : ℝ)) := fun hzero =>
  brownian_not_ae_zero (D.W.W 0) zero_lt_one
    ((solvesBSDEJ_zero_generator_Y_terminal h).symm.trans hzero)
end Backward

/-! ### The witness -/

/-- Some probability space carries a Lévy driver with one Brownian coordinate and Lebesgue mark
intensity whose count on the window `(0, 1] × ℝ` is almost surely infinite, whose count on the
box `(0, 1] × [0, 1]` generates a nontrivial σ-algebra, whose Itô–Lévy integral of the mark
indicator `1_{[0,1]}` has second moment `1` on `[0, 1]`, and over which the backward equation
with vanishing generator, terminal datum `W_1` and horizon `1` has a solution triple, every
solution triple having a value process that is not almost surely `0` at the horizon. -/
theorem exists_levyDriver_infinite_activity :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyDriver P 1 (volume : Measure ℝ)),
      (∀ᵐ ω ∂P, D.N.N ω stepRegion = ⊤) ∧
        MeasurableSpace.comap (fun ω => D.N.N ω markBox) inferInstance ≠ ⊥ ∧
        ∫⁻ ω, (‖markWindowIntegral D 1 ω‖₊ : ℝ≥0∞) ^ 2 ∂P = 1 ∧
        (∃ (Y : ℝ → Ω → ℝ) (Z : ℝ → Ω → (Fin 1 → ℝ)) (U : ℝ → Ω → ℝ → ℝ),
            SolvesBSDEJ D (fun _ _ _ _ => (0 : ℝ)) (fun ω => (D.W.W 0).W 1 ω) 1 Y Z U) ∧
        ∀ (Y : ℝ → Ω → ℝ) (Z : ℝ → Ω → (Fin 1 → ℝ)) (U : ℝ → Ω → ℝ → ℝ),
          SolvesBSDEJ D (fun _ _ _ _ => (0 : ℝ)) (fun ω => (D.W.W 0).W 1 ω) 1 Y Z U →
            ¬ (Y 1 =ᵐ[P] fun _ => (0 : ℝ)) := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ := Driver.LevyDriver.exists 1 ℝ (volume : Measure ℝ)
  exact ⟨Ω, inferInstance, P, inferInstance, D, count_stepRegion_ae_eq_top D.N,
    regionSigma_markBox_ne_bot D, lintegral_sq_markWindowIntegral D,
    (exists_unique_solvesBSDEJ_volume D).1,
    fun _ _ _ h => solvesBSDEJ_zero_generator_Y_not_ae_zero h⟩
end LevyStochCalc.Examples.Nonvacuity


