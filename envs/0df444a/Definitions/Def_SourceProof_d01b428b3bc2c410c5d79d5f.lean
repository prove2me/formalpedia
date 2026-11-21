-- Prove2me | Definitions.Def_SourceProof_d01b428b3bc2c410c5d79d5f
-- name    : SourceProof_d01b428b3bc2c410c5d79d5f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:20:16.828786+00:00
-- url     : https://prove2.me/theorems/744f7478-754d-491c-9b05-267455819078
-- title:
--   LevyStochCalc source module: SourceProof_d01b428b3bc2c410c5d79d5f
-- statement:
--   The original source theorem `LevyStochCalc.Ito.Picard.lintegral_sq_iSup_picardSelfMapRaw_lt_top` comes from the `LevyStochCalc.Ito.PicardSupL2` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardContractionFixedPoint_F001
import Definitions.Def_LevyStochCalc_Ito_PicardContractionFixedPoint_F002
import Definitions.Def_LevyStochCalc_Probability_DoobContinuous_F002
import Definitions.Def_LevyStochCalc_Probability_DoobContinuous_F003
import Definitions.Def_SourceProof_11a8326171366cbd17e7e143

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The `S²` bound for the Picard step

`LevyStochCalc.Ito.Setting.JumpDiffusion.sup_L2` asks for `𝔼[sup_{t ≤ T} ‖X_t‖²] < ∞`, the `S²`
norm, which is stronger than the weighted supremum of `L²` norms the Picard space carries. The
Picard step splits into a drift, `d` Brownian integrals and a compensated-Poisson integral; the
drift is bounded pathwise by its own total variation over the window, and each stochastic
component is a martingale, so Doob's `L²` inequality over the dyadic points applies. Only the
dyadic form of Doob is available here, because the stochastic integrals are càdlàg only up to
modification.
-/

open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}

/-! ### An elementary two-term bound -/

/-! ### The drift component -/

/-! ### The stochastic components -/

variable {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]

/-! ### The whole step -/

/-! ### The `S²` bound for the raw self-map -/


theorem _root_.Prove2MeSourceProof.h_d01b428b3bc2c410c5d79d5f
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
    (hZb : bieleckiNorm (P := P) 0 T Z < ⊤) {T' : ℝ} (hT' : 0 < T') :
    ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i,
        (‖(picardSelfMapRaw W N ℱ hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT hZm hZa hZb).X
          (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤ := by
  set Y := LevyStochCalc.Ito.Picard.picardSelfMapRaw W N ℱ hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT hZm hZa hZb with hY
  set St := LevyStochCalc.Ito.Picard.picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip hZm hZa hZb hT.le x₀ with hSt
  have hZsm : Measurable (Function.uncurry fun (s : ℝ) (ω : Ω) => Z (min s T) ω) :=
    hZm.comp ((measurable_fst.min measurable_const).prodMk measurable_snd)
  have hZe := LevyStochCalc.Ito.Picard.lintegral_sq_rawStop_lt_top hZm hZb hT.le
  -- the step at the frozen process has finite `S²` norm
  have hstep : ∀ i : Fin n, ∫⁻ ω,
      (⨆ m, (‖LevyStochCalc.Probability.dyadicRunMax (fun t ω => St t ω i) T' m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P < ⊤ := fun i =>
    _root_.Prove2MeSourceProof.h_11a8326171366cbd17e7e143 W N ℱ hℱW hℱN coeffs
      (fun s ω => Z (min s T) ω) x₀
      (LevyStochCalc.Ito.Picard.measurable_sigma_rawStop coeffs hReg hZm T)
      (LevyStochCalc.Ito.Picard.progressivelyMeasurable_sigma_rawStop coeffs hReg hZa T)
      (fun i' j _ hb => _root_.Prove2MeSourceProof.h_bdaa282fd363a3be48f8fdce coeffs hReg hLip
        (Z := fun s ω => Z (min s T) ω) hZsm hZe i' j hb)
      (LevyStochCalc.Ito.Picard.measurable_gamma_rawStop coeffs hReg hZm T)
      (LevyStochCalc.Ito.Picard.markedProgressivelyMeasurable_gamma_rawStop coeffs hReg hZa T)
      (fun i' _ hb => _root_.Prove2MeSourceProof.h_e554e55fb9c1def6b7e8b55b coeffs hReg hLip
        (Z := fun s ω => Z (min s T) ω) hZsm hZe i' hb)
      (LevyStochCalc.Ito.Picard.measurable_mu_rawStop coeffs hReg hZm T)
      (fun i' b hb => _root_.Prove2MeSourceProof.h_946b446a671aae16e8dcf40a coeffs hReg hLip
        (Z := fun s ω => Z (min s T) ω) hZe i' hb)
      i hT'
  -- the modification agrees at all dyadic points simultaneously
  have hae : ∀ᵐ ω ∂P, ∀ p : ℕ × ℕ, Y.X (LevyStochCalc.Probability.dyadicTime T' p.1 p.2) ω
      = St (LevyStochCalc.Probability.dyadicTime T' p.1 p.2) ω := by
    rw [MeasureTheory.ae_all_iff]
    exact fun p => _root_.Prove2MeSourceProof.h_b732528cf57a7c0dad8dceb7 W N ℱ hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT
      hZm hZa hZb (LevyStochCalc.Probability.dyadicTime T' p.1 p.2)
  have hcad : ∀ᵐ ω ∂P, ∀ (i : Fin n) (t : ℝ),
      Filter.Tendsto (fun s => Y.X s ω i) (nhdsWithin t (Set.Ioi t)) (nhds (Y.X t ω i)) := by
    filter_upwards [Y.cadlag_paths] with ω hω i t
    exact ((continuous_apply i).tendsto _).comp (hω t).1
  have hStm : ∀ i : Fin n, ∀ t : ℝ, Measurable fun ω => St t ω i := fun i t =>
    _root_.Prove2MeSourceProof.h_e264a15a5a2a191954307942 W N ℱ hℱW hℱN coeffs hReg hLip x₀
      hZm hZa hZb hT.le t i
  calc ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Y.X (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P
      ≤ ∫⁻ ω, ∑ i, (⨆ m, (‖LevyStochCalc.Probability.dyadicRunMax (fun t ω => St t ω i) T' m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P := by
        refine lintegral_mono_ae ?_
        filter_upwards [hae, hcad] with ω hω hc
        refine le_trans (LevyStochCalc.Probability.iSup_sum_sq_le (fun t ω => Y.X t ω) T' ω) (le_of_eq ?_)
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [_root_.Prove2MeSourceProof.h_755d31da2fec92eb2a10cfd6 hT'.le (hc i)]
        congr 1
        refine iSup_congr fun m => ?_
        rw [_root_.Prove2MeSourceProof.h_d00ab70a6365c7b4a03cc45a, _root_.Prove2MeSourceProof.h_d00ab70a6365c7b4a03cc45a]
        exact iSup_congr fun k => by rw [congrFun (hω (m, (k : ℕ))) i]
    _ = ∑ i, ∫⁻ ω, (⨆ m, (‖LevyStochCalc.Probability.dyadicRunMax (fun t ω => St t ω i) T' m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P :=
        lintegral_finsetSum _ fun i _ =>
          (Measurable.iSup fun m => LevyStochCalc.Probability.measurable_enorm_dyadicRunMax (hStm i) T' m).pow_const 2
    _ < ⊤ := ENNReal.sum_lt_top.mpr fun i _ => hstep i
end LevyStochCalc.Ito.Picard


