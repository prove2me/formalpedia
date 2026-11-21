-- Prove2me | Definitions.Def_SourceProof_e319076aff1b47a860ce2705
-- name    : SourceProof_e319076aff1b47a860ce2705
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:24:49.412519+00:00
-- url     : https://prove2.me/theorems/196020f8-b97d-4988-8b1e-83a06304621e
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Ito.Picard.picardStep_drift_diff_lintegral_sq_bound
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardBieleckiNorm_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The Picard map for jump-diffusion SDEs

The vector-norm and `ω`-integrated forms of the drift Lipschitz estimate; the Bielecki
exponential-weight calculus `∫_0^t e^{2βs} ds = (e^{2βt} - 1) / (2β)` together with the
weighted-integral bound and the contraction-rate threshold it yields; the joint measurability of
the coefficients `σ` and `γ` composed with a process; and the Picard map `picardStep` itself, the
sum of the initial value, the drift integral, the Brownian component `picardStep_diffusion` and
the compensated-Poisson component `picardStep_jump`.
-/
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

omit [MeasurableSpace E] in

theorem _root_.Prove2MeSourceProof.h_e319076aff1b47a860ce2705
    {n d : ℕ} (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P]
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    {L_μ : ℝ} (_hL_μ_nn : 0 ≤ L_μ)
    (_h_μ_lip : ∀ s : ℝ, ∀ x₁ x₂ : Fin n → ℝ, ∀ i : Fin n,
      |coeffs.μ s x₁ i - coeffs.μ s x₂ i| ≤ L_μ * ‖x₁ - x₂‖)
    (X Y : ℝ → Ω → (Fin n → ℝ))
    (x₀ : Fin n → ℝ)
    (t : ℝ) (ht : 0 ≤ t)
    -- Almost-everywhere integrability hypotheses (the pointwise bound only
    -- holds for ω with all integrands well-defined):
    (h_bound_ae : ∀ᵐ ω ∂P,
      (∑ i : Fin n, ((picardStep_drift (E := E) coeffs X x₀ t ω
          - picardStep_drift coeffs Y x₀ t ω) i) ^ 2)
        ≤ (n : ℝ) * L_μ ^ 2 * t *
            ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2)
    -- Nonnegativity of the per-ω inner integral (for ENNReal conversion):
    (h_inner_nn : ∀ᵐ ω ∂P, 0 ≤
      ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2) :
    ∫⁻ ω, ENNReal.ofReal (∑ i : Fin n,
      ((picardStep_drift (E := E) coeffs X x₀ t ω
          - picardStep_drift coeffs Y x₀ t ω) i) ^ 2) ∂P
    ≤ ENNReal.ofReal ((n : ℝ) * L_μ ^ 2 * t) *
        ∫⁻ ω, ENNReal.ofReal
          (∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2) ∂P := by
  -- Monotonicity of lintegral applied to the a.e. bound.
  have h_pointwise_ennreal : ∀ᵐ ω ∂P,
      ENNReal.ofReal (∑ i : Fin n,
        ((LevyStochCalc.Ito.Picard.picardStep_drift (E := E) coeffs X x₀ t ω
            - LevyStochCalc.Ito.Picard.picardStep_drift coeffs Y x₀ t ω) i) ^ 2)
      ≤ ENNReal.ofReal ((n : ℝ) * L_μ ^ 2 * t) *
          ENNReal.ofReal (∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2) := by
    filter_upwards [h_bound_ae, h_inner_nn] with ω h_bd h_inner_nn
    rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (n : ℝ) * L_μ ^ 2 * t)]
    exact ENNReal.ofReal_le_ofReal h_bd
  calc ∫⁻ ω, ENNReal.ofReal (∑ i : Fin n,
      ((LevyStochCalc.Ito.Picard.picardStep_drift (E := E) coeffs X x₀ t ω
          - LevyStochCalc.Ito.Picard.picardStep_drift coeffs Y x₀ t ω) i) ^ 2) ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal ((n : ℝ) * L_μ ^ 2 * t) *
          ENNReal.ofReal (∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2) ∂P :=
        MeasureTheory.lintegral_mono_ae h_pointwise_ennreal
    _ = ENNReal.ofReal ((n : ℝ) * L_μ ^ 2 * t) *
        ∫⁻ ω, ENNReal.ofReal (∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2) ∂P :=
        MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
/-! ## Map of the contraction argument

The Picard map `picardStep` and its three components are defined above,
together with the drift-component Lipschitz estimates. The rest of the
argument is:

1. `integral_sq_le_mul_integral_sq_on_Icc` (above) — the `L²`
   Cauchy–Schwarz bound `(∫_0^t f)² ≤ t · ∫_0^t f²` behind the
   Bielecki-norm contraction estimate.
2. `picardStep_diffusion_diff_lipschitz_sq_componentwise` — the Lipschitz
   bound of the Brownian component, via the `L²`-isometry of the integral
   difference (`itoIsometry_diff_brownian`) and the Lipschitz hypothesis on
   `σ`.
3. `picardStep_jump_diff_lipschitz_sq_componentwise` — the Lipschitz bound
   of the compensated-Poisson component, via `itoIsometry_diff_compensated`
   and the Lipschitz hypothesis on `γ`.
4. `picardStep_bielecki_contraction`, `picardStep_bielecki_contraction_tight`
   — the map is a Bielecki contraction once `β` is large relative to the
   Lipschitz constant; `bieleckiNorm_picardStep_diff_le`
   (`Ito/PicardOutput.lean`) is the form the well-posedness proof uses, and
   `bieleckiNorm_picardSelfMap_diff_le` (`Ito/PicardContraction.lean`) its
   transfer to the self-map of the process space.
5. `picardIter`, `picardLimit` (`Ito/PicardContraction.lean`, on
   `bieleckiLimit` of `Ito/PicardLimit.lean`) and
   `picardSelfMapRaw_isFixedPoint` — the iterates converge and the limit is
   a fixed point.
6. `exists_solvesOn`, `ae_eq_of_solvesOn` (`Ito/PicardWindow.lean`),
   `exists_globalSolution` (`Ito/PicardGlobal.lean`) and
   `exists_jumpDiffusion_unique_of_solvesOn` (`Ito/PicardWellPosed.lean`)
   — the fixed point solves the SDE on each window, is unique there, and
   the windows glue to a strong solution on `[0, ∞)`; `Ito/PicardFixedPoint.lean`
   restates the result as `LevyStochCalc.Ito.Setting.JumpDiffusion.exists_unique`. -/

end LevyStochCalc.Ito.Picard


