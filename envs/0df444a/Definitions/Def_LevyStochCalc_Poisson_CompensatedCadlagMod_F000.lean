-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedCadlagMod_F000
-- name    : LevyStochCalc_Poisson_CompensatedCadlagMod_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:09:43.120471+00:00
-- url     : https://prove2.me/theorems/c87ea7dd-dac4-4097-b208-64426b0fad5e
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedCadlagMod
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedCadlagMod. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_Compensated_F001
import Definitions.Def_LevyStochCalc_Probability_ProgressiveCadlag_F000
import Definitions.Def_LevyStochCalc_Probability_ProgressiveCadlag_F001
import Definitions.Def_SourceProof_1720d71b3049591278c59d6d

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# An everywhere-càdlàg modification of the compensated Itô–Lévy integral

The `L²` Itô–Lévy integral `stochasticIntegral` is adapted to the right-continuous filtration
and its paths are càdlàg outside a `P`-null set. When that null set is `ℱ 0`-measurable and the
filtration is constant before time `0`, replacing the integral by `0` there gives a modification
whose paths are càdlàg at *every* sample point; such a process is progressively measurable, hence
jointly measurable in the sample point and the time.

## Main definitions

* `LevyStochCalc.Poisson.Compensated.cadlagIntegral` — the everywhere-càdlàg modification of the
  compensated integral.
* `LevyStochCalc.Poisson.Compensated.cadlagIntegralPi` — the same for one member of a finite
  family of integrands.

## Main statements

* `LevyStochCalc.Poisson.Compensated.exists_everywhere_cadlag_stochasticIntegral` — the
  compensated integral has an adapted modification whose every path is càdlàg.
* `LevyStochCalc.Poisson.Compensated.measurable_uncurry_cadlagIntegral` — that modification is
  jointly measurable in the sample point and the time.
* `LevyStochCalc.Poisson.Compensated.measurable_uncurry_cadlagIntegralPi` — the vector form, for
  a `Fin n`-indexed family of integrands.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, §4.2.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

section Modification

variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : IsPoissonFiltration N ℱ)
  (φ : Ω → ℝ → E → ℝ)
  (h_meas : Measurable (fun (p : Ω × ℝ × E) => φ p.1 p.2.1 p.2.2))
  (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (h_sq_int_global : ∀ T : ℝ, 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
  (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
  (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)

include hℱ0 hnull in
/-- The compensated integral has a modification, adapted to the right-continuous filtration,
whose path at every sample point is right-continuous with left limits. -/
theorem exists_everywhere_cadlag_stochasticIntegral :
    ∃ Y : ℝ → Ω → ℝ, Adapted ℱ.rightCont Y ∧
      (∀ t : ℝ, Y t =ᵐ[P] stochasticIntegral N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t) ∧
      (∀ (ω : Ω) (t : ℝ), Tendsto (fun s => Y s ω) (𝓝[>] t) (𝓝 (Y t ω))) ∧
      ∀ (ω : Ω) (t : ℝ), ∃ L : ℝ, Tendsto (fun s => Y s ω) (𝓝[<] t) (𝓝 L) := by
  obtain ⟨Y, hYmeas, hYae, hYright, hYleft⟩ :=
    _root_.Prove2MeSourceProof.h_1720d71b3049591278c59d6d
      (P := P) (ℱ := ℱ.rightCont) hℱ0
      (fun s hs h0 => (ℱ.le_rightCont 0) _ (hnull s hs h0))
      (stochasticIntegral_adapted N ℱ hℱ φ h_meas h_progMeas h_sq_int_global)
      (stochasticIntegral_cadlag N ℱ hℱ φ h_meas h_progMeas h_sq_int_global)
  exact ⟨Y, hYmeas, hYae, hYright, hYleft⟩
/-- The everywhere-càdlàg modification of the `L²` Itô–Lévy integral
`M_t = ∫_0^t ∫_E φ(s, e) Ñ(ds, de)`. -/
noncomputable def cadlagIntegral (T : ℝ) : Ω → ℝ :=
  Classical.choose (exists_everywhere_cadlag_stochasticIntegral N ℱ hℱ φ h_meas h_progMeas
    h_sq_int_global hℱ0 hnull) T
/-- The everywhere-càdlàg modification is adapted to the right-continuous filtration. -/
theorem cadlagIntegral_adapted :
    Adapted ℱ.rightCont
      (cadlagIntegral N ℱ hℱ φ h_meas h_progMeas h_sq_int_global hℱ0 hnull) :=
  (Classical.choose_spec (exists_everywhere_cadlag_stochasticIntegral N ℱ hℱ φ h_meas
    h_progMeas h_sq_int_global hℱ0 hnull)).1
/-- The everywhere-càdlàg modification agrees almost surely with the stochastic integral at
every time. -/
theorem cadlagIntegral_ae_eq (t : ℝ) :
    cadlagIntegral N ℱ hℱ φ h_meas h_progMeas h_sq_int_global hℱ0 hnull t
      =ᵐ[P] stochasticIntegral N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t :=
  (Classical.choose_spec (exists_everywhere_cadlag_stochasticIntegral N ℱ hℱ φ h_meas
    h_progMeas h_sq_int_global hℱ0 hnull)).2.1 t
/-- Every path of the everywhere-càdlàg modification is right-continuous. -/
theorem cadlagIntegral_rightContinuous (ω : Ω) (t : ℝ) :
    Tendsto (fun s => cadlagIntegral N ℱ hℱ φ h_meas h_progMeas h_sq_int_global hℱ0 hnull s ω)
      (𝓝[>] t)
      (𝓝 (cadlagIntegral N ℱ hℱ φ h_meas h_progMeas h_sq_int_global hℱ0 hnull t ω)) :=
  (Classical.choose_spec (exists_everywhere_cadlag_stochasticIntegral N ℱ hℱ φ h_meas
    h_progMeas h_sq_int_global hℱ0 hnull)).2.2.1 ω t
/-- Every path of the everywhere-càdlàg modification has a left limit at every time. -/
theorem cadlagIntegral_exists_leftLim (ω : Ω) (t : ℝ) :
    ∃ L : ℝ, Tendsto
      (fun s => cadlagIntegral N ℱ hℱ φ h_meas h_progMeas h_sq_int_global hℱ0 hnull s ω)
      (𝓝[<] t) (𝓝 L) :=
  (Classical.choose_spec (exists_everywhere_cadlag_stochasticIntegral N ℱ hℱ φ h_meas
    h_progMeas h_sq_int_global hℱ0 hnull)).2.2.2 ω t
/-- The everywhere-càdlàg modification is progressively measurable for the right-continuous
filtration. -/
theorem progressivelyMeasurable_cadlagIntegral :
    Probability.ProgressivelyMeasurable ℱ.rightCont
      (fun ω s => cadlagIntegral N ℱ hℱ φ h_meas h_progMeas h_sq_int_global hℱ0 hnull s ω) :=
  _root_.Prove2MeSourceProof.h_845c55972b82cdb43dfb6421
    (cadlagIntegral_adapted N ℱ hℱ φ h_meas h_progMeas h_sq_int_global hℱ0 hnull)
    (cadlagIntegral_rightContinuous N ℱ hℱ φ h_meas h_progMeas h_sq_int_global hℱ0 hnull)
/-- The everywhere-càdlàg modification is jointly measurable in the sample point and the
time. -/
theorem measurable_uncurry_cadlagIntegral :
    Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) =>
      cadlagIntegral N ℱ hℱ φ h_meas h_progMeas h_sq_int_global hℱ0 hnull s ω) :=
  (LevyStochCalc.Probability.measurable_uncurry_of_rightContinuous
    (cadlagIntegral_adapted N ℱ hℱ φ h_meas h_progMeas h_sq_int_global hℱ0 hnull)
    (cadlagIntegral_rightContinuous N ℱ hℱ φ h_meas h_progMeas h_sq_int_global hℱ0
      hnull)).comp measurable_swap
end Modification

section Pi

variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : IsPoissonFiltration N ℱ)
  (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
  (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
  {n : ℕ} (Φ : Fin n → Ω → ℝ → E → ℝ)
  (hΦm : ∀ i : Fin n, Measurable (fun (p : Ω × ℝ × E) => Φ i p.1 p.2.1 p.2.2))
  (hΦp : ∀ i : Fin n, Probability.MarkedProgressivelyMeasurable ℱ (Φ i))
  (hΦq : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖Φ i ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

/-- The everywhere-càdlàg modification of the compensated integral of the `i`-th member of a
finite family of integrands. -/
noncomputable def cadlagIntegralPi (i : Fin n) : ℝ → Ω → ℝ :=
  cadlagIntegral N ℱ hℱ (Φ i) (hΦm i) (hΦp i) (hΦq i) hℱ0 hnull
/-- Each member of the family is adapted to the right-continuous filtration. -/
theorem cadlagIntegralPi_adapted (i : Fin n) :
    Adapted ℱ.rightCont (cadlagIntegralPi N ℱ hℱ hℱ0 hnull Φ hΦm hΦp hΦq i) :=
  cadlagIntegral_adapted N ℱ hℱ (Φ i) (hΦm i) (hΦp i) (hΦq i) hℱ0 hnull
/-- Every path of the family is right-continuous, coordinatewise and hence in `Fin n → ℝ`. -/
theorem cadlagIntegralPi_rightContinuous (ω : Ω) (t : ℝ) :
    Tendsto (fun s i => cadlagIntegralPi N ℱ hℱ hℱ0 hnull Φ hΦm hΦp hΦq i s ω) (𝓝[>] t)
      (𝓝 fun i => cadlagIntegralPi N ℱ hℱ hℱ0 hnull Φ hΦm hΦp hΦq i t ω) :=
  tendsto_pi_nhds.mpr fun i =>
    cadlagIntegral_rightContinuous N ℱ hℱ (Φ i) (hΦm i) (hΦp i) (hΦq i) hℱ0 hnull ω t
/-- Every path of the family has left limits in `Fin n → ℝ` at every time. -/
theorem cadlagIntegralPi_exists_leftLim (ω : Ω) (t : ℝ) :
    ∃ L : Fin n → ℝ,
      Tendsto (fun s i => cadlagIntegralPi N ℱ hℱ hℱ0 hnull Φ hΦm hΦp hΦq i s ω) (𝓝[<] t)
        (𝓝 L) := by
  choose L hL using fun i : Fin n =>
    cadlagIntegral_exists_leftLim N ℱ hℱ (Φ i) (hΦm i) (hΦp i) (hΦq i) hℱ0 hnull ω t
  exact ⟨L, tendsto_pi_nhds.mpr hL⟩
/-- At every time the family agrees with the stochastic integrals almost surely, on one event
covering all `n` coordinates. -/
theorem cadlagIntegralPi_ae_eq (t : ℝ) :
    (fun ω i => cadlagIntegralPi N ℱ hℱ hℱ0 hnull Φ hΦm hΦp hΦq i t ω)
      =ᵐ[P] fun ω i => stochasticIntegral N ℱ hℱ (Φ i) (hΦm i) (hΦp i) (hΦq i) t ω := by
  filter_upwards [MeasureTheory.ae_all_iff.mpr fun i : Fin n =>
    cadlagIntegral_ae_eq N ℱ hℱ (Φ i) (hΦm i) (hΦp i) (hΦq i) hℱ0 hnull t] with ω hω
  exact funext fun i => hω i
/-- The family is jointly measurable in the sample point and the time. -/
theorem measurable_uncurry_cadlagIntegralPi :
    Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) (i : Fin n) =>
      cadlagIntegralPi N ℱ hℱ hℱ0 hnull Φ hΦm hΦp hΦq i s ω) :=
  measurable_pi_lambda _ fun i =>
    measurable_uncurry_cadlagIntegral N ℱ hℱ (Φ i) (hΦm i) (hΦp i) (hΦq i) hℱ0 hnull
end Pi

end LevyStochCalc.Poisson.Compensated


