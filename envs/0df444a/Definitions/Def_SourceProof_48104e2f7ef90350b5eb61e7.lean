-- Prove2me | Definitions.Def_SourceProof_48104e2f7ef90350b5eb61e7
-- name    : SourceProof_48104e2f7ef90350b5eb61e7
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:59:21.474062+00:00
-- url     : https://prove2.me/theorems/c5925bef-9a2b-40ab-b5be-33d30e54f251
-- title:
--   LevyStochCalc source module: SourceProof_48104e2f7ef90350b5eb61e7
-- statement:
--   The original source theorem `LevyStochCalc.Ito.Picard.lintegral_sq_picardStep_diff_le` comes from the `LevyStochCalc.Ito.PicardOutputStepDiff` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardOutputStepDiff_F000
import Definitions.Def_SourceProof_8353ec6e796401c7d3295bd3
import Definitions.Def_SourceProof_a4be34a312401dc6dd6575e8

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The contraction estimate for the Picard step

The Picard step is the sum of its drift, diffusion and jump components, so the three
per-component difference bounds combine, through `‖a + b + c‖² ≤ 3(‖a‖² + ‖b‖² + ‖c‖²)`,
into a single per-time second-moment bound for the difference of two steps by the energy of
the difference of the two frozen paths. Weighting that bound back into the Bielecki norm
gives a contraction factor that tends to `0` as the rate `β` grows.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
variable {n d : ℕ} {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]

section Weighting

-- `picardStep` and the two stochastic-integral components unfold to `Finset` sums over `Fin d`
-- and to the `L²`-limit integrals; the statement below repeats those terms verbatim on both
-- sides, so unfolding them during unification only costs time. Sealed as in `Ito/Picard.lean`.
attribute [local irreducible] picardStep picardStep_diffusion picardStep_jump
attribute [local irreducible]
  LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral
attribute [local irreducible] LevyStochCalc.Brownian.Ito.stochasticIntegral

set_option maxHeartbeats 4000000 in
-- The statement names the full three-component Picard term twice, once along each path, and
-- elaborating the second application exceeds the default budget even with the components sealed.

theorem _root_.Prove2MeSourceProof.h_48104e2f7ef90350b5eb61e7
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (X Y : ℝ → Ω → (Fin n → ℝ)) (x₀ : Fin n → ℝ)
    (h_σ_meas_X : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    (h_σ_progMeas_X : ∀ i : Fin n, ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (X s ω) i j))
    (h_σ_sq_X : ∀ i : Fin n, ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_γ_meas_X : ∀ i : Fin n,
      Measurable (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
    (h_γ_progMeas_X : ∀ i : Fin n,
      Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (X s ω) e i))
    (h_γ_sq_X : ∀ i : Fin n, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (h_σ_meas_Y : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (Y s ω) i j)))
    (h_σ_progMeas_Y : ∀ i : Fin n, ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (Y s ω) i j))
    (h_σ_sq_Y : ∀ i : Fin n, ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.σ s (Y s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_γ_meas_Y : ∀ i : Fin n,
      Measurable (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (Y p.2.1 p.1) p.2.2 i))
    (h_γ_progMeas_Y : ∀ i : Fin n,
      Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (Y s ω) e i))
    (h_γ_sq_Y : ∀ i : Fin n, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖coeffs.γ s (Y s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hμX : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X s ω) i))
    (hμY : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (Y s ω) i))
    (hXYm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => ‖X s ω - Y s ω‖))
    (hμXsq : ∀ i : Fin n, ∀ b : ℝ, 0 < b → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hμYsq : ∀ i : Fin n, ∀ b : ℝ, 0 < b → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      (‖coeffs.μ s (Y s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hXYsq : ∀ b : ℝ, 0 < b → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t) :
    ∫⁻ ω, ∑ i : Fin n,
        (‖picardStep W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas_X h_σ_progMeas_X h_σ_sq_X
              h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω i
          - picardStep W N ℱ hℱW hℱN coeffs Y x₀ h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y
              h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ 3 * (ENNReal.ofReal ((n : ℝ) * L ^ 2 * t)
              + ENNReal.ofReal ((n : ℝ) * ((d : ℝ) * L ^ 2))
              + ENNReal.ofReal ((n : ℝ) * L ^ 2))
          * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
              (∑ i, (‖X s ω i - Y s ω i‖₊ : ℝ≥0∞) ^ 2) ∂volume ∂P := by
  have hbridge : ∀ ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume
      ≤ ∫⁻ s in Set.Icc (0 : ℝ) t, (∑ i, (‖X s ω i - Y s ω i‖₊ : ℝ≥0∞) ^ 2) ∂volume :=
    fun ω => lintegral_mono fun s => by
      simpa [Pi.sub_apply] using LevyStochCalc.Ito.Picard.sq_coe_nnnorm_le_sum (X s ω - Y s ω)
  have hbridgeR : (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
          (∑ i, (‖X s ω i - Y s ω i‖₊ : ℝ≥0∞) ^ 2) ∂volume ∂P :=
    lintegral_mono hbridge
  have hbochner : (∫⁻ ω, ENNReal.ofReal
        (∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2 ∂volume) ∂P)
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
          (∑ i, (‖X s ω i - Y s ω i‖₊ : ℝ≥0∞) ^ 2) ∂volume ∂P := by
    refine lintegral_mono fun ω => ?_
    refine le_trans (LevyStochCalc.Ito.Picard.lintegral_window_norm_le_sum (Z := fun s ω => X s ω - Y s ω) t ω)
      (lintegral_mono fun s => ?_)
    exact le_of_eq (Finset.sum_congr rfl fun i _ => by rw [Pi.sub_apply])
  have hsplit : ∀ (ω : Ω) (i : Fin n),
      LevyStochCalc.Ito.Picard.picardStep W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas_X h_σ_progMeas_X h_σ_sq_X
          h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω i
        - LevyStochCalc.Ito.Picard.picardStep W N ℱ hℱW hℱN coeffs Y x₀ h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y
            h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω i
      = (LevyStochCalc.Ito.Picard.picardStep_drift coeffs X x₀ t ω i - LevyStochCalc.Ito.Picard.picardStep_drift coeffs Y x₀ t ω i)
        + (LevyStochCalc.Ito.Picard.picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω i
            - LevyStochCalc.Ito.Picard.picardStep_diffusion W ℱ hℱW coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω i)
        + (LevyStochCalc.Ito.Picard.picardStep_jump N ℱ hℱN coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω i
            - LevyStochCalc.Ito.Picard.picardStep_jump N ℱ hℱN coeffs Y h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω i) := by
    intro ω i
    rw [LevyStochCalc.Ito.Picard.picardStep_apply_eq W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas_X h_σ_progMeas_X h_σ_sq_X
      h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω i,
      LevyStochCalc.Ito.Picard.picardStep_apply_eq W N ℱ hℱW hℱN coeffs Y x₀ h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y
        h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω i]
    ring
  rw [lintegral_congr fun ω => Finset.sum_congr rfl fun i _ => by rw [hsplit ω i]]
  refine LevyStochCalc.Ito.Picard.lintegral_sq_sum3_le
    (U₁ := fun ω i => LevyStochCalc.Ito.Picard.picardStep_drift coeffs X x₀ t ω i
      - LevyStochCalc.Ito.Picard.picardStep_drift coeffs Y x₀ t ω i)
    (U₂ := fun ω i =>
      LevyStochCalc.Ito.Picard.picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω i
        - LevyStochCalc.Ito.Picard.picardStep_diffusion W ℱ hℱW coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω i)
    (U₃ := fun ω i =>
      LevyStochCalc.Ito.Picard.picardStep_jump N ℱ hℱN coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω i
        - LevyStochCalc.Ito.Picard.picardStep_jump N ℱ hℱN coeffs Y h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω i)
    (fun i => ((((LevyStochCalc.Ito.Picard.measurable_picardStep_drift coeffs X x₀ i (hμX i) t).sub
      (LevyStochCalc.Ito.Picard.measurable_picardStep_drift coeffs Y x₀ i (hμY i) t)).nnnorm).coe_nnreal_ennreal).pow_const
        2)
    (fun i => ((((_root_.Prove2MeSourceProof.h_06ce725b2f140e9df5ff737b W ℱ hℱW coeffs X h_σ_meas_X h_σ_progMeas_X
      h_σ_sq_X i t).sub (_root_.Prove2MeSourceProof.h_06ce725b2f140e9df5ff737b W ℱ hℱW coeffs Y h_σ_meas_Y
        h_σ_progMeas_Y h_σ_sq_Y i t)).nnnorm).coe_nnreal_ennreal).pow_const 2)
    (fun i => ((((LevyStochCalc.Ito.Picard.measurable_picardStep_jump N ℱ hℱN coeffs X h_γ_meas_X h_γ_progMeas_X
      h_γ_sq_X i t).sub (LevyStochCalc.Ito.Picard.measurable_picardStep_jump N ℱ hℱN coeffs Y h_γ_meas_Y
        h_γ_progMeas_Y h_γ_sq_Y i t)).nnnorm).coe_nnreal_ennreal).pow_const 2)
    ?_ ?_ ?_
  · rw [← LevyStochCalc.Ito.Picard.lintegral_ofReal_sum_sq_eq]
    exact (LevyStochCalc.Ito.Picard.drift_diff_lintegral_sq_bound coeffs hLip.1 (LevyStochCalc.Ito.Picard.mu_lip_componentwise coeffs hLip) X Y x₀
      hμX hμY hXYm hμXsq hμYsq hXYsq ht.le).trans (mul_le_mul' le_rfl hbochner)
  · exact (_root_.Prove2MeSourceProof.h_a4be34a312401dc6dd6575e8 W ℱ hℱW coeffs hLip.1 hLip.2.2.1 X Y
      h_σ_meas_X h_σ_meas_Y h_σ_progMeas_X h_σ_progMeas_Y h_σ_sq_X h_σ_sq_Y ht).trans
      (mul_le_mul' le_rfl hbridgeR)
  · exact (_root_.Prove2MeSourceProof.h_8353ec6e796401c7d3295bd3 N ℱ hℱN coeffs hLip X Y h_γ_meas_X h_γ_progMeas_X
      h_γ_sq_X h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y ht).trans (mul_le_mul' le_rfl hbridgeR)
end Weighting

end LevyStochCalc.Ito.Picard


