-- Prove2me | Definitions.Def_SourceProof_b732528cf57a7c0dad8dceb7
-- name    : SourceProof_b732528cf57a7c0dad8dceb7
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:45:22.989724+00:00
-- url     : https://prove2.me/theorems/901c295e-fa6a-41e7-9322-ae80450d4efc
-- title:
--   LevyStochCalc source module: SourceProof_b732528cf57a7c0dad8dceb7
-- statement:
--   The original source theorem `LevyStochCalc.Ito.Picard.picardSelfMapRaw_ae_eq` comes from the `LevyStochCalc.Ito.PicardOutputModification` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardOutputModification_F002

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

end Modification

section SelfMap

variable {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]


theorem _root_.Prove2MeSourceProof.h_b732528cf57a7c0dad8dceb7
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) [ℱ.IsRightContinuous]
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) {T : ℝ} (hT : 0 < T)
    {Z : ℝ → Ω → (Fin n → ℝ)} (hZm : Measurable (Function.uncurry Z))
    (hZa : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω i)
    (hZb : bieleckiNorm (P := P) 0 T Z < ⊤) (t : ℝ) :
    (picardSelfMapRaw W N ℱ hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT hZm hZa hZb).X t
      =ᵐ[P] picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip hZm hZa hZb hT.le x₀ t :=
  Classical.choose_spec (_root_.Prove2MeSourceProof.h_eb845cc7a87885afac3d8843 W ℱ hℱW coeffs
    (fun s ω => Z (min s T) ω)
    (LevyStochCalc.Ito.Picard.measurable_sigma_rawStop coeffs hReg hZm T)
    (LevyStochCalc.Ito.Picard.progressivelyMeasurable_sigma_rawStop coeffs hReg hZa T)
    (fun i j _ hT' => _root_.Prove2MeSourceProof.h_bdaa282fd363a3be48f8fdce coeffs hReg hLip
      (Z := fun s ω => Z (min s T) ω)
      (hZm.comp ((measurable_fst.min measurable_const).prodMk measurable_snd))
      (LevyStochCalc.Ito.Picard.lintegral_sq_rawStop_lt_top hZm hZb hT.le) i j hT')
    N hℱN x₀
    (LevyStochCalc.Ito.Picard.measurable_gamma_rawStop coeffs hReg hZm T)
    (LevyStochCalc.Ito.Picard.markedProgressivelyMeasurable_gamma_rawStop coeffs hReg hZa T)
    (fun i _ hT' => _root_.Prove2MeSourceProof.h_e554e55fb9c1def6b7e8b55b coeffs hReg hLip
      (Z := fun s ω => Z (min s T) ω)
      (hZm.comp ((measurable_fst.min measurable_const).prodMk measurable_snd))
      (LevyStochCalc.Ito.Picard.lintegral_sq_rawStop_lt_top hZm hZb hT.le) i hT')
    hℱ0 hnull
    (LevyStochCalc.Ito.Picard.measurable_mu_rawStop coeffs hReg hZm T)
    (LevyStochCalc.Ito.Picard.progressivelyMeasurable_mu_rawStop coeffs hReg hZa T)
    (fun i _ hb => _root_.Prove2MeSourceProof.h_946b446a671aae16e8dcf40a coeffs hReg hLip
      (Z := fun s ω => Z (min s T) ω)
      (LevyStochCalc.Ito.Picard.lintegral_sq_rawStop_lt_top hZm hZb hT.le) i hb)
    (fun i => _root_.Prove2MeSourceProof.h_946b446a671aae16e8dcf40a coeffs hReg hLip
      (Z := fun s ω => Z (min s T) ω)
      (LevyStochCalc.Ito.Picard.lintegral_sq_rawStop_lt_top hZm hZb hT.le) i hT)
    (fun i j => _root_.Prove2MeSourceProof.h_bdaa282fd363a3be48f8fdce coeffs hReg hLip
      (Z := fun s ω => Z (min s T) ω)
      (hZm.comp ((measurable_fst.min measurable_const).prodMk measurable_snd))
      (LevyStochCalc.Ito.Picard.lintegral_sq_rawStop_lt_top hZm hZb hT.le) i j hT)
    (fun i => _root_.Prove2MeSourceProof.h_e554e55fb9c1def6b7e8b55b coeffs hReg hLip
      (Z := fun s ω => Z (min s T) ω)
      (hZm.comp ((measurable_fst.min measurable_const).prodMk measurable_snd))
      (LevyStochCalc.Ito.Picard.lintegral_sq_rawStop_lt_top hZm hZb hT.le) i hT)) t
end SelfMap

end LevyStochCalc.Ito.Picard


