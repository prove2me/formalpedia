-- Prove2me | Definitions.Def_SourceProof_7d42b3f858f0e2725802728a
-- name    : SourceProof_7d42b3f858f0e2725802728a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:32:40.502159+00:00
-- url     : https://prove2.me/theorems/2cc5dd7a-444d-4f8e-9283-a455e5180323
-- title:
--   LevyStochCalc source module: SourceProof_7d42b3f858f0e2725802728a
-- statement:
--   The original source theorem `LevyStochCalc.Ito.Picard.picardStep_jump_diff_lipschitz_sq_componentwise` comes from the `LevyStochCalc.Ito.PicardStochasticLipschitz` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardStepMap_F000
import Definitions.Def_LevyStochCalc_Ito_PicardStepMap_F001
import Mathlib.Algebra.Order.Chebyshev

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Lipschitz estimates for the stochastic components of the Picard map

The `L²`-isometry `𝔼|∫_0^T H₁ dW - ∫_0^T H₂ dW|² = 𝔼 ∫_0^T |H₁ - H₂|² ds` for the difference of
two Brownian Itô integrals, the discrete Cauchy-Schwarz inequality and the `ℝ≥0∞` norm-square
identities it is combined with, and the resulting per-component `L²` Lipschitz bounds for the
diffusion and the jump component of the Picard map in terms of the Lipschitz constants of `σ` and
`γ`.
-/
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian.Ito

variable {Ω : Type*} [MeasurableSpace Ω]

end LevyStochCalc.Brownian.Ito

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

end LevyStochCalc.Ito.Picard

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]


theorem _root_.Prove2MeSourceProof.h_7d42b3f858f0e2725802728a
    {n d : ℕ}
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    {L_γ : ℝ} (_hL_γ_nn : 0 ≤ L_γ)
    (X Y : ℝ → Ω → (Fin n → ℝ))
    (i : Fin n)
    -- L²-in-e Lipschitz hypothesis on γ (ENNReal form, pointwise in (s, ω)):
    (h_γ_lip : ∀ s : ℝ, ∀ ω : Ω,
      ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i - coeffs.γ s (Y s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν
        ≤ ENNReal.ofReal (L_γ ^ 2) * (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2)
    -- Hypothesis bundles for `picardStep_jump` well-typedness — X side:
    (hX_meas : ∀ i : Fin n,
      Measurable (fun (p : Ω × ℝ × E) => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
    (hX_progMeas : ∀ i : Fin n,
      Probability.MarkedProgressivelyMeasurable ℱ
        (fun ω s e => coeffs.γ s (X s ω) e i))
    (hX_sq : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    -- Hypothesis bundles — Y side:
    (hY_meas : ∀ i : Fin n,
      Measurable (fun (p : Ω × ℝ × E) => coeffs.γ p.2.1 (Y p.2.1 p.1) p.2.2 i))
    (hY_progMeas : ∀ i : Fin n,
      Probability.MarkedProgressivelyMeasurable ℱ
        (fun ω s e => coeffs.γ s (Y s ω) e i))
    (hY_sq : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (Y s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, (‖picardStep_jump (E := E) N ℱ hℱN coeffs X hX_meas hX_progMeas hX_sq T ω i
            - picardStep_jump N ℱ hℱN coeffs Y hY_meas hY_progMeas hY_sq T ω i‖₊
          : ℝ≥0∞) ^ 2 ∂P
      ≤ ENNReal.ofReal (L_γ ^ 2) *
          ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  -- Step 1: unfold `picardStep_jump` (definitional) so the LHS is exactly
  -- the L²-norm-squared of the difference of two `Compensated.stochasticIntegral`
  -- outputs, matching the LHS of `itoIsometry_diff_compensated`.
  -- `picardStep_jump` is `noncomputable def`-ed as
  --   `fun i => Compensated.stochasticIntegral N ℱ hℱN
  --     (fun ω' s e => γ s (X s ω') e i) ... T ω`
  -- so the lemma's LHS is, by `unfold + simp only [picardStep_jump]`,
  -- exactly the LHS of `itoIsometry_diff_compensated` with
  --   φ₁ ω' s e := γ s (X s ω') e i
  --   φ₂ ω' s e := γ s (Y s ω') e i.
  -- Step 2: apply the isometry to get equality with the inner double-lintegral
  -- of `‖γ(s, X_s, e) i − γ(s, Y_s, e) i‖²`.
  have h_iso := LevyStochCalc.Poisson.Compensated.itoIsometry_diff_compensated
    N ℱ hℱN (fun ω' s e => coeffs.γ s (X s ω') e i)
      (fun ω' s e => coeffs.γ s (Y s ω') e i)
    (hX_meas i) (hY_meas i)
    (hX_progMeas i) (hY_progMeas i)
    (hX_sq i) (hY_sq i) T hT
  -- Rewriting the LHS via the isometry turns the goal into the bound
  -- `inner double lintegral ≤ ENNReal.ofReal L_γ²
  --   · ∫⁻ ω ∫⁻ s, ‖X-Y‖² ∂volume ∂P`.
  -- `picardStep_jump i` unfolds definitionally to the `Compensated.stochasticIntegral`
  -- of `γ ... i`, so the rewrite goes through `show`+`exact_mod_cast`.
  simp only [LevyStochCalc.Ito.Picard.picardStep_jump] at *
  rw [h_iso]
  -- Goal now:
  -- ∫⁻ ω, ∫⁻ s in [0,T], ∫⁻ e,
  --   ‖γ(s, X_s, e) i − γ(s, Y_s, e) i‖² ν⊗ds ∂P
  --   ≤ ENNReal.ofReal L_γ² · ∫⁻ ω, ∫⁻ s in [0,T], ‖X_s ω − Y_s ω‖² ds ∂P
  -- Step 3: apply the Lipschitz hypothesis h_γ_lip pointwise in (s, ω) under
  -- the inner ν-integral.  This gives a chain through `lintegral_mono`.
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        ((‖coeffs.γ s (X s ω) e i - coeffs.γ s (Y s ω) e i‖₊ : ℝ≥0∞)) ^ 2
          ∂ν ∂volume ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (ENNReal.ofReal (L_γ ^ 2) * (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2)
            ∂volume ∂P := by
        refine lintegral_mono fun ω => ?_
        refine lintegral_mono fun s => ?_
        exact h_γ_lip s ω
    _ = ∫⁻ ω, ENNReal.ofReal (L_γ ^ 2) *
            ∫⁻ s in Set.Icc (0 : ℝ) T,
              (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
        refine lintegral_congr fun ω => ?_
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (L_γ ^ 2) *
          ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
end LevyStochCalc.Ito.Picard


