-- Prove2me | Definitions.Def_LevyStochCalc_Ito_PicardOutputModification_F001
-- name    : LevyStochCalc_Ito_PicardOutputModification_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:33:02.480347+00:00
-- url     : https://prove2.me/theorems/f1728103-b9a1-4d76-bfcf-6935757c9235
-- title:
--   Source declarations: LevyStochCalc.Ito.PicardOutputModification
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.PicardOutputModification. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardOutputModification_F000
import Definitions.Def_SourceProof_1f982f95c243b7704e920390
import Definitions.Def_SourceProof_4dc182a98fe43374f6dd9730
import Definitions.Def_SourceProof_f512774c3d012a8b87c44ec5

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Càdlàg modifications of the Picard step

The `L²` stochastic integral is defined separately at each time, so the Picard step as first
written has no path regularity. Replacing each Brownian component by a càdlàg adapted
modification, and the drift by its almost surely continuous version, produces a process
indistinguishable from the step at every fixed time and càdlàg along almost every path; the
Bielecki norm is unchanged, and the result is a genuine self-map of the space of bounded
adapted càdlàg processes.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
variable {n d : ℕ} {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]

omit [MeasurableSpace E] [MeasureTheory.IsProbabilityMeasure P] in
/-- Almost every path of a process with locally finite energy is locally integrable. -/
theorem ae_integrableOn_of_lintegral_sq {f : Ω → ℝ → ℝ}
    (hf : Measurable (Function.uncurry f))
    (hfin : ∀ b : ℝ, 0 < b →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∀ᵐ ω ∂P, ∀ b : ℝ, MeasureTheory.IntegrableOn (f ω) (Set.Icc (0 : ℝ) b) volume := by
  filter_upwards [_root_.Prove2MeSourceProof.h_f512774c3d012a8b87c44ec5 hf hfin] with ω hω b
  haveI : MeasureTheory.IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) b)) :=
    ⟨by rw [MeasureTheory.Measure.restrict_apply_univ, Real.volume_Icc]
        exact ENNReal.ofReal_lt_top⟩
  exact (hω b).integrable (by norm_num)
omit [MeasurableSpace E] [MeasureTheory.IsProbabilityMeasure P] in
/-- **Almost every drift path of the Picard step is continuous.** -/
theorem ae_continuous_picardStep_drift
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ)) (x₀ : Fin n → ℝ) (i : Fin n)
    (h_μ_meas : Measurable (Function.uncurry fun ω s => coeffs.μ s (X s ω) i))
    (h_μ_sq : ∀ b : ℝ, 0 < b → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∀ᵐ ω ∂P, Continuous fun t => picardStep_drift coeffs X x₀ t ω i := by
  filter_upwards [ae_integrableOn_of_lintegral_sq h_μ_meas h_μ_sq] with ω hω
  have : (fun t => picardStep_drift coeffs X x₀ t ω i)
      = fun t => x₀ i + ∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X s ω) i := rfl
  rw [this]
  exact continuous_const.add (_root_.Prove2MeSourceProof.h_1f982f95c243b7704e920390 hω)
omit [MeasurableSpace E] in
/-- The Bielecki norm depends on the process only through its almost-everywhere class at each
time, so a modification has the same norm. -/
theorem bieleckiNorm_congr_ae (β T : ℝ) {Y Z : ℝ → Ω → (Fin n → ℝ)}
    (h : ∀ t : ℝ, Y t =ᵐ[P] Z t) :
    bieleckiNorm (P := P) β T Y = bieleckiNorm (P := P) β T Z := by
  unfold bieleckiNorm
  refine iSup_congr fun t => iSup_congr fun _ => ?_
  have hinner : (∫⁻ ω, ∑ i, (‖Y t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P)
      = ∫⁻ ω, ∑ i, (‖Z t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [h t] with ω hω
    rw [hω]
  rw [hinner]
section Modification

variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
variable (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
variable (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
variable (X : ℝ → Ω → (Fin n → ℝ))
variable (h_σ_meas : ∀ i : Fin n, ∀ j : Fin d,
  Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
variable (h_σ_progMeas : ∀ i : Fin n, ∀ j : Fin d,
  Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (X s ω) i j))
variable (h_σ_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
  ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

/-- A càdlàg representative of the `(i, j)` Brownian integral along `X`. -/
noncomputable def sigmaMod (i : Fin n) (j : Fin d) : ℝ → Ω → ℝ :=
  Classical.choose (exists_cadlag_modification_itoIntegral (W.W j) ℱ (hℱW j)
    (fun ω s => coeffs.σ s (X s ω) i j) (h_σ_meas i j) (h_σ_progMeas i j) (h_σ_sq i j))
omit [MeasurableSpace E] in
theorem sigmaMod_adapted (i : Fin n) (j : Fin d) :
    MeasureTheory.Adapted ℱ.rightCont
      (sigmaMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq i j) :=
  (Classical.choose_spec (exists_cadlag_modification_itoIntegral (W.W j) ℱ (hℱW j)
    (fun ω s => coeffs.σ s (X s ω) i j) (h_σ_meas i j) (h_σ_progMeas i j) (h_σ_sq i j))).1
omit [MeasurableSpace E] in
theorem sigmaMod_ae_eq (i : Fin n) (j : Fin d) (t : ℝ) :
    sigmaMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq i j t
      =ᵐ[P] LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W j) ℱ (hℱW j)
        (fun ω s => coeffs.σ s (X s ω) i j)
        (h_σ_meas i j) (h_σ_progMeas i j) (h_σ_sq i j) t :=
  (Classical.choose_spec (exists_cadlag_modification_itoIntegral (W.W j) ℱ (hℱW j)
    (fun ω s => coeffs.σ s (X s ω) i j) (h_σ_meas i j) (h_σ_progMeas i j)
      (h_σ_sq i j))).2.1 t
omit [MeasurableSpace E] in
theorem sigmaMod_cadlag (i : Fin n) (j : Fin d) :
    ∀ᵐ ω ∂P, ∀ t : ℝ,
      Filter.Tendsto (fun s => sigmaMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq i j s ω)
          (nhdsWithin t (Set.Ioi t))
          (nhds (sigmaMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq i j t ω)) ∧
        ∃ L : ℝ, Filter.Tendsto
          (fun s => sigmaMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq i j s ω)
          (nhdsWithin t (Set.Iio t)) (nhds L) :=
  (Classical.choose_spec (exists_cadlag_modification_itoIntegral (W.W j) ℱ (hℱW j)
    (fun ω s => coeffs.σ s (X s ω) i j) (h_σ_meas i j) (h_σ_progMeas i j)
      (h_σ_sq i j))).2.2
variable {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
variable (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
variable (x₀ : Fin n → ℝ)
variable (h_γ_meas : ∀ i : Fin n,
  Measurable (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
variable (h_γ_progMeas : ∀ i : Fin n,
  Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (X s ω) e i))
variable (h_γ_sq : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
  ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
    (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

/-- **The Picard step with a càdlàg representative of its Brownian component.**

`picardStep` is an `L²` limit taken separately at each time, so it is not jointly measurable as
it stands; this replaces its Brownian component by the càdlàg modification of C0d-2, which
changes it only on a null set at each time. -/
noncomputable def picardStepMod : ℝ → Ω → (Fin n → ℝ) :=
  fun t ω i => picardStep_drift coeffs X x₀ t ω i
    + (∑ j : Fin d, sigmaMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq i j t ω)
    + picardStep_jump N ℱ hℱN coeffs X h_γ_meas h_γ_progMeas h_γ_sq t ω i
/-- The modified step is a modification of the Picard step. -/
theorem picardStepMod_ae_eq (t : ℝ) :
    picardStepMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq N hℱN x₀
        h_γ_meas h_γ_progMeas h_γ_sq t
      =ᵐ[P] picardStep W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas h_σ_progMeas h_σ_sq
        h_γ_meas h_γ_progMeas h_γ_sq t := by
  have hall : ∀ᵐ ω ∂P, ∀ p : Fin n × Fin d,
      sigmaMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq p.1 p.2 t ω
        = LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W p.2) ℱ (hℱW p.2)
            (fun ω' s => coeffs.σ s (X s ω') p.1 p.2)
            (h_σ_meas p.1 p.2) (h_σ_progMeas p.1 p.2) (h_σ_sq p.1 p.2) t ω :=
    MeasureTheory.ae_all_iff.mpr fun p => sigmaMod_ae_eq W ℱ hℱW coeffs X h_σ_meas
      h_σ_progMeas h_σ_sq p.1 p.2 t
  filter_upwards [hall] with ω hω
  funext i
  change picardStep_drift coeffs X x₀ t ω i
      + (∑ j : Fin d, sigmaMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq i j t ω)
      + picardStep_jump N ℱ hℱN coeffs X h_γ_meas h_γ_progMeas h_γ_sq t ω i
    = _
  simp only [picardStep, Pi.add_apply, picardStep_diffusion,
    LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral]
  exact congrArg₂ (· + ·)
    (congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun j _ => hω (i, j))) rfl
/-- The modified step has the same Bielecki norm as the Picard step. -/
theorem bieleckiNorm_picardStepMod (β T : ℝ) :
    bieleckiNorm (P := P) β T
        (picardStepMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq N hℱN x₀
          h_γ_meas h_γ_progMeas h_γ_sq)
      = bieleckiNorm (P := P) β T
        (fun t ω => picardStep W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas h_σ_progMeas h_σ_sq
          h_γ_meas h_γ_progMeas h_γ_sq t ω) :=
  bieleckiNorm_congr_ae β T fun t => picardStepMod_ae_eq W ℱ hℱW coeffs X h_σ_meas
    h_σ_progMeas h_σ_sq N hℱN x₀ h_γ_meas h_γ_progMeas h_γ_sq t
/-- The modified step is adapted to the right-continuous filtration. -/
theorem picardStepMod_adapted
    (h_μ_progMeas : ∀ i : Fin n,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.μ s (X s ω) i))
    (i : Fin n) (t : ℝ) :
    Measurable[ℱ.rightCont t] fun ω =>
      picardStepMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq N hℱN x₀
        h_γ_meas h_γ_progMeas h_γ_sq t ω i := by
  have hdrift : Measurable[ℱ.rightCont t] fun ω => picardStep_drift coeffs X x₀ t ω i :=
    ((_root_.Prove2MeSourceProof.h_4dc182a98fe43374f6dd9730
      (h_μ_progMeas i) t).mono (ℱ.le_rightCont t) le_rfl).const_add _
  have hσ : ∀ j : Fin d, Measurable[ℱ.rightCont t] fun ω =>
      sigmaMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq i j t ω :=
    fun j => sigmaMod_adapted W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq i j t
  have hγ : Measurable[ℱ.rightCont t] fun ω =>
      picardStep_jump N ℱ hℱN coeffs X h_γ_meas h_γ_progMeas h_γ_sq t ω i :=
    (LevyStochCalc.Poisson.Compensated.stochasticIntegral_adapted N ℱ hℱN
      (fun ω s e => coeffs.γ s (X s ω) e i) (h_γ_meas i) (h_γ_progMeas i)
        (h_γ_sq i) t).stronglyMeasurable.measurable
  exact (hdrift.add (Finset.measurable_sum _ fun j _ => hσ j)).add hγ
/-- Almost every path of the modified step is càdlàg. -/
theorem picardStepMod_cadlag
    (h_μ_meas : ∀ i : Fin n,
      Measurable (Function.uncurry fun ω s => coeffs.μ s (X s ω) i))
    (h_μ_sq : ∀ i : Fin n, ∀ b : ℝ, 0 < b →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
        (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (i : Fin n) :
    ∀ᵐ ω ∂P, ∀ t : ℝ,
      Filter.Tendsto (fun s => picardStepMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq
            N hℱN x₀ h_γ_meas h_γ_progMeas h_γ_sq s ω i)
          (nhdsWithin t (Set.Ioi t))
          (nhds (picardStepMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq
            N hℱN x₀ h_γ_meas h_γ_progMeas h_γ_sq t ω i)) ∧
        ∃ L : ℝ, Filter.Tendsto
          (fun s => picardStepMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq
            N hℱN x₀ h_γ_meas h_γ_progMeas h_γ_sq s ω i)
          (nhdsWithin t (Set.Iio t)) (nhds L) := by
  have hσall : ∀ᵐ ω ∂P, ∀ j : Fin d, ∀ t : ℝ,
      Filter.Tendsto (fun s => sigmaMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq i j s ω)
          (nhdsWithin t (Set.Ioi t))
          (nhds (sigmaMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq i j t ω)) ∧
        ∃ L : ℝ, Filter.Tendsto
          (fun s => sigmaMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq i j s ω)
          (nhdsWithin t (Set.Iio t)) (nhds L) :=
    MeasureTheory.ae_all_iff.mpr fun j =>
      sigmaMod_cadlag W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq i j
  filter_upwards [ae_continuous_picardStep_drift coeffs X x₀ i (h_μ_meas i) (h_μ_sq i),
    hσall,
    LevyStochCalc.Poisson.Compensated.stochasticIntegral_cadlag N ℱ hℱN
      (fun ω s e => coeffs.γ s (X s ω) e i) (h_γ_meas i) (h_γ_progMeas i) (h_γ_sq i)]
    with ω hdr hσ hγ t
  have hright := ((hdr.continuousAt (x := t)).continuousWithinAt (s := Set.Ioi t)).tendsto
  refine ⟨((hright.add (tendsto_finsetSum _ fun j _ => (hσ j t).1)).add (hγ t).1), ?_⟩
  choose L hL using fun j : Fin d => (hσ j t).2
  obtain ⟨Lγ, hLγ⟩ := (hγ t).2
  refine ⟨picardStep_drift coeffs X x₀ t ω i + (∑ j : Fin d, L j) + Lγ, ?_⟩
  exact ((((hdr.continuousAt (x := t)).continuousWithinAt (s := Set.Iio t)).tendsto.add
    (tendsto_finsetSum _ fun j _ => hL j)).add hLγ)
end Modification

section SelfMap

variable {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]

end SelfMap

end LevyStochCalc.Ito.Picard


