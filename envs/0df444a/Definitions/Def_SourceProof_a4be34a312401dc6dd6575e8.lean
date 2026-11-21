-- Prove2me | Definitions.Def_SourceProof_a4be34a312401dc6dd6575e8
-- name    : SourceProof_a4be34a312401dc6dd6575e8
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:44:25.228706+00:00
-- url     : https://prove2.me/theorems/c1ca4118-a5a8-4ddd-9bce-2033746201de
-- title:
--   LevyStochCalc source module: SourceProof_a4be34a312401dc6dd6575e8
-- statement:
--   The original source theorem `LevyStochCalc.Ito.Picard.diffusion_diff_lintegral_sq_bound` comes from the `LevyStochCalc.Ito.PicardOutputWeighting` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardOutputModification_F001
import Definitions.Def_LevyStochCalc_Ito_PicardOutputModification_F002
import Definitions.Def_SourceProof_06ce725b2f140e9df5ff737b
import Definitions.Def_SourceProof_d52fae11d2865b46132e568a

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Bielecki weighting and the per-component difference bounds

The Bielecki norm with rate `β` dominates the second moment at each time of `[0, T]` after
reweighting by `e^{2βs}`, and the doubly-integrated energy over `[0, t]` by
`e^{2βt}/(2β)`, the factor `1/(2β)` being what makes the Picard rate small for large `β`.
Combined with the Lipschitz bounds on the coefficients this bounds the drift, diffusion and
jump components of the difference of two Picard steps by the energy of the difference of the
two frozen paths.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
variable {n d : ℕ} {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]

section Weighting

omit [MeasurableSpace E] in

theorem _root_.Prove2MeSourceProof.h_a4be34a312401dc6dd6575e8
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    {L_σ : ℝ} (hL_σ_nn : 0 ≤ L_σ)
    (h_σ_lip : ∀ s : ℝ, ∀ x₁ x₂ : Fin n → ℝ,
      (∑ i : Fin n, ∑ j : Fin d, (coeffs.σ s x₁ i j - coeffs.σ s x₂ i j) ^ 2)
        ≤ L_σ ^ 2 * ‖x₁ - x₂‖ ^ 2)
    (X Y : ℝ → Ω → (Fin n → ℝ))
    (h_σ_meas_X : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    (h_σ_meas_Y : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (Y s ω) i j)))
    (h_σ_progMeas_X : ∀ i : Fin n, ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (X s ω) i j))
    (h_σ_progMeas_Y : ∀ i : Fin n, ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (Y s ω) i j))
    (h_σ_sq_X : ∀ i : Fin n, ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_σ_sq_Y : ∀ i : Fin n, ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.σ s (Y s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t) :
    ∫⁻ ω, ∑ i : Fin n,
        (‖picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω i
          - picardStep_diffusion W ℱ hℱW coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω i‖₊
          : ℝ≥0∞) ^ 2 ∂P
      ≤ ENNReal.ofReal ((n : ℝ) * ((d : ℝ) * L_σ ^ 2))
          * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
              (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  have hmeas : ∀ i : Fin n, Measurable fun ω =>
      (‖LevyStochCalc.Ito.Picard.picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω i
        - LevyStochCalc.Ito.Picard.picardStep_diffusion W ℱ hℱW coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω i‖₊
        : ℝ≥0∞) ^ 2 := fun i =>
    ((((_root_.Prove2MeSourceProof.h_06ce725b2f140e9df5ff737b W ℱ hℱW coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X i
      t).sub (_root_.Prove2MeSourceProof.h_06ce725b2f140e9df5ff737b W ℱ hℱW coeffs Y h_σ_meas_Y h_σ_progMeas_Y
        h_σ_sq_Y i t)).nnnorm).coe_nnreal_ennreal).pow_const 2
  rw [MeasureTheory.lintegral_finsetSum _ fun i _ => hmeas i]
  calc ∑ i : Fin n, ∫⁻ ω,
        (‖LevyStochCalc.Ito.Picard.picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω i
          - LevyStochCalc.Ito.Picard.picardStep_diffusion W ℱ hℱW coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω i‖₊
          : ℝ≥0∞) ^ 2 ∂P
      ≤ ∑ _i : Fin n, ENNReal.ofReal ((d : ℝ) * L_σ ^ 2)
          * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
              (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
        Finset.sum_le_sum fun i _ =>
          _root_.Prove2MeSourceProof.h_d52fae11d2865b46132e568a W ℱ hℱW coeffs hL_σ_nn h_σ_lip
            X Y i h_σ_meas_X h_σ_meas_Y h_σ_progMeas_X h_σ_progMeas_Y h_σ_sq_X h_σ_sq_Y t ht
    _ = ENNReal.ofReal ((n : ℝ) * ((d : ℝ) * L_σ ^ 2))
          * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
              (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg n), ← mul_assoc]
        congr 2
        simp
end Weighting

end LevyStochCalc.Ito.Picard


