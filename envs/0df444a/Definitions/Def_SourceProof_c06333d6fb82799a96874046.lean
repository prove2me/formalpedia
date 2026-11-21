-- Prove2me | Definitions.Def_SourceProof_c06333d6fb82799a96874046
-- name    : SourceProof_c06333d6fb82799a96874046
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:23:25.838974+00:00
-- url     : https://prove2.me/theorems/0020393f-9374-44ce-b9b2-3bf923bd7fd7
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Ito.Picard.picardStep_drift_diff_lipschitz_sq_componentwise
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardBieleckiNorm_F001
import Definitions.Def_SourceProof_afc5f2e9c8f3a3e4d632ea4b

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Bielecki norm, the process space `S²`, and the drift step of Picard iteration

The Bielecki-weighted `L²` norm `‖X‖_{β,T} = sup_{t ∈ [0,T]} e^{-βt} (𝔼‖X_t‖²)^{1/2}` of a
process on `[0, T]`, the space `SBoundedProcess` of jointly measurable, progressively measurable,
almost surely càdlàg processes of finite norm at weight `0`, and the freeze of such a process at
the horizon, which leaves the norm unchanged and is `L²`-bounded at every later time.  The drift
component `picardStep_drift` of the Picard map is defined here, with its per-component difference
identities, its `L¹` Lipschitz bound, the Cauchy-Schwarz bound `(∫_0^t f)² ≤ t ∫_0^t f²` on a
window, and the per-component `L²` Lipschitz bound that follows from them.
-/
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

namespace SBoundedProcess

end SBoundedProcess

omit [MeasurableSpace Ω] [MeasurableSpace E] in

theorem _root_.Prove2MeSourceProof.h_c06333d6fb82799a96874046
    {n d : ℕ}
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    {L_μ : ℝ} (hL_μ_nn : 0 ≤ L_μ)
    (h_μ_lip : ∀ s : ℝ, ∀ x₁ x₂ : Fin n → ℝ, ∀ i : Fin n,
      |coeffs.μ s x₁ i - coeffs.μ s x₂ i| ≤ L_μ * ‖x₁ - x₂‖)
    (X Y : ℝ → Ω → (Fin n → ℝ))
    (x₀ : Fin n → ℝ)
    (t : ℝ) (ht : 0 ≤ t) (ω : Ω) (i : Fin n)
    (h_X_int : MeasureTheory.IntegrableOn
      (fun s => coeffs.μ s (X s ω) i) (Set.Icc (0 : ℝ) t) MeasureTheory.volume)
    (h_Y_int : MeasureTheory.IntegrableOn
      (fun s => coeffs.μ s (Y s ω) i) (Set.Icc (0 : ℝ) t) MeasureTheory.volume)
    (h_XY_diff_int : MeasureTheory.IntegrableOn
      (fun s => ‖X s ω - Y s ω‖) (Set.Icc (0 : ℝ) t) MeasureTheory.volume)
    (h_XY_diff_sq_L2 : MeasureTheory.MemLp
      (fun s => ‖X s ω - Y s ω‖) 2
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) t))) :
    ((picardStep_drift (E := E) coeffs X x₀ t ω
        - picardStep_drift coeffs Y x₀ t ω) i) ^ 2
      ≤ L_μ ^ 2 * t *
          ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2 := by
  -- Step 1: L¹ Lipschitz bound (proven).
  have h_L1 := LevyStochCalc.Ito.Picard.picardStep_drift_diff_lipschitz_componentwise
    coeffs hL_μ_nn h_μ_lip X Y x₀ t ω i h_X_int h_Y_int h_XY_diff_int
  -- The L¹ bound's |·| is the abs of the i-th component diff.
  -- Square both sides (LHS² = (|·|)² = (·)², RHS² = L² · (∫‖X-Y‖)²).
  have h_abs_sq : ((LevyStochCalc.Ito.Picard.picardStep_drift (E := E) coeffs X x₀ t ω
        - LevyStochCalc.Ito.Picard.picardStep_drift coeffs Y x₀ t ω) i) ^ 2
      = |(LevyStochCalc.Ito.Picard.picardStep_drift (E := E) coeffs X x₀ t ω
          - LevyStochCalc.Ito.Picard.picardStep_drift coeffs Y x₀ t ω) i| ^ 2 := by
    rw [sq_abs]
  rw [h_abs_sq]
  -- |·|² ≤ (L_μ · ∫‖X-Y‖)² by squaring h_L1 (both sides nonneg).
  have h_abs_nn : 0 ≤ |(LevyStochCalc.Ito.Picard.picardStep_drift (E := E) coeffs X x₀ t ω
        - LevyStochCalc.Ito.Picard.picardStep_drift coeffs Y x₀ t ω) i| := abs_nonneg _
  have h_int_nn : 0 ≤ ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ :=
    MeasureTheory.integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun _ => norm_nonneg _)
  have h_RHS_nn : 0 ≤ L_μ * ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ :=
    mul_nonneg hL_μ_nn h_int_nn
  have h_sq_bound := mul_self_le_mul_self h_abs_nn h_L1
  -- h_sq_bound: |·| * |·| ≤ (L_μ · ∫‖X-Y‖) * (L_μ · ∫‖X-Y‖)
  -- Convert ·*· to ·^2 on both sides:
  have h_LHS_sq_eq : |(LevyStochCalc.Ito.Picard.picardStep_drift (E := E) coeffs X x₀ t ω
        - LevyStochCalc.Ito.Picard.picardStep_drift coeffs Y x₀ t ω) i| *
      |(LevyStochCalc.Ito.Picard.picardStep_drift coeffs X x₀ t ω
          - LevyStochCalc.Ito.Picard.picardStep_drift coeffs Y x₀ t ω) i|
      = |(LevyStochCalc.Ito.Picard.picardStep_drift coeffs X x₀ t ω
          - LevyStochCalc.Ito.Picard.picardStep_drift coeffs Y x₀ t ω) i| ^ 2 := by ring
  have h_RHS_sq_eq : (L_μ * ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖) *
      (L_μ * ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖)
      = L_μ ^ 2 * (∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖) ^ 2 := by ring
  rw [h_LHS_sq_eq, h_RHS_sq_eq] at h_sq_bound
  -- Apply Cauchy-Schwarz: (∫ ‖X-Y‖)² ≤ t · ∫ ‖X-Y‖².
  have h_CS := _root_.Prove2MeSourceProof.h_afc5f2e9c8f3a3e4d632ea4b
    (fun s => ‖X s ω - Y s ω‖) t ht
    (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    h_XY_diff_sq_L2
  -- Chain: |·|² ≤ L_μ² · (∫‖X-Y‖)² ≤ L_μ² · t · ∫‖X-Y‖².
  have h_L_sq_nn : 0 ≤ L_μ ^ 2 := sq_nonneg _
  have h_CS_mul : L_μ ^ 2 * (∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖) ^ 2
      ≤ L_μ ^ 2 * (t * ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2) :=
    mul_le_mul_of_nonneg_left h_CS h_L_sq_nn
  calc |(LevyStochCalc.Ito.Picard.picardStep_drift (E := E) coeffs X x₀ t ω
        - LevyStochCalc.Ito.Picard.picardStep_drift coeffs Y x₀ t ω) i| ^ 2
      ≤ L_μ ^ 2 * (∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖) ^ 2 := h_sq_bound
    _ ≤ L_μ ^ 2 * (t * ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2) := h_CS_mul
    _ = L_μ ^ 2 * t * ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2 := by ring
end LevyStochCalc.Ito.Picard


