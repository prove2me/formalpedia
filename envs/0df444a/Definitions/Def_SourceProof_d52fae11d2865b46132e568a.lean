-- Prove2me | Definitions.Def_SourceProof_d52fae11d2865b46132e568a
-- name    : SourceProof_d52fae11d2865b46132e568a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:42:32.015105+00:00
-- url     : https://prove2.me/theorems/373f09a1-7324-4340-922c-66842627b26e
-- title:
--   LevyStochCalc source module: SourceProof_d52fae11d2865b46132e568a
-- statement:
--   The original source theorem `LevyStochCalc.Ito.Picard.picardStep_diffusion_diff_lipschitz_sq_componentwise` comes from the `LevyStochCalc.Ito.PicardStochasticLipschitz` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_1a2c983c4a1fa7387543aefa

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

omit [MeasurableSpace E] in

theorem _root_.Prove2MeSourceProof.h_d52fae11d2865b46132e568a
    {n d : ℕ}
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    {L_σ : ℝ} (_hL_σ_nn : 0 ≤ L_σ)
    -- Componentwise Lipschitz hypothesis on σ (matches `JumpDiffusionCoeffs.IsLipschitz`):
    -- `∑_{i,j} (σ(s, x₁)_{ij} - σ(s, x₂)_{ij})² ≤ L_σ² · ‖x₁ - x₂‖²`
    (h_σ_lip : ∀ s : ℝ, ∀ x₁ x₂ : Fin n → ℝ,
      (∑ i : Fin n, ∑ j : Fin d,
        (coeffs.σ s x₁ i j - coeffs.σ s x₂ i j) ^ 2)
        ≤ L_σ ^ 2 * ‖x₁ - x₂‖ ^ 2)
    (X Y : ℝ → Ω → (Fin n → ℝ))
    (i : Fin n)
    -- Per-(i', j) measurability / progressive-measurability / L²
    -- hypotheses for σ along X and Y, threaded to `picardStep_diffusion`.
    (h_σ_meas_X : ∀ i' : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i' j)))
    (h_σ_meas_Y : ∀ i' : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (Y s ω) i' j)))
    (h_σ_progMeas_X : ∀ i' : Fin n, ∀ j : Fin d,
        Probability.ProgressivelyMeasurable ℱ
          (fun ω s => coeffs.σ s (X s ω) i' j))
    (h_σ_progMeas_Y : ∀ i' : Fin n, ∀ j : Fin d,
        Probability.ProgressivelyMeasurable ℱ
          (fun ω s => coeffs.σ s (Y s ω) i' j))
    (h_σ_sq_X : ∀ i' : Fin n, ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.σ s (X s ω) i' j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_σ_sq_Y : ∀ i' : Fin n, ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.σ s (Y s ω) i' j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, (‖picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X T ω i
              - picardStep_diffusion W ℱ hℱW coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y T ω i‖₊
            : ℝ≥0∞) ^ 2 ∂P
      ≤ ENNReal.ofReal ((d : ℝ) * L_σ ^ 2) *
          ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  -- Abbreviation for the per-j 1D Brownian integrals (X and Y branches).
  set Mx : Fin d → Ω → ℝ := fun j ω =>
    LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W j) ℱ (hℱW j)
      (fun ω' s => coeffs.σ s (X s ω') i j)
      (h_σ_meas_X i j) (h_σ_progMeas_X i j) (h_σ_sq_X i j) T ω with hMx
  set My : Fin d → Ω → ℝ := fun j ω =>
    LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W j) ℱ (hℱW j)
      (fun ω' s => coeffs.σ s (Y s ω') i j)
      (h_σ_meas_Y i j) (h_σ_progMeas_Y i j) (h_σ_sq_Y i j) T ω with hMy
  -- The 1D Brownian Itô integral returned by `stochasticIntegral` is a
  -- martingale (`martingale_stochasticIntegral`); each `Mx j T`, `My j T`
  -- is `StronglyMeasurable` w.r.t. the filtration's σ-algebra (a
  -- sub-σ-algebra of the ambient one), and so is measurable w.r.t. the
  -- ambient by `Measurable.mono`.
  have hMx_meas : ∀ j : Fin d, Measurable (Mx j) := by
    intro j
    obtain ⟨Filt, hMart⟩ := LevyStochCalc.Brownian.Ito.martingale_stochasticIntegral
      (W.W j) ℱ (hℱW j) (fun ω' s => coeffs.σ s (X s ω') i j)
      (h_σ_meas_X i j) (h_σ_progMeas_X i j) (h_σ_sq_X i j)
    have h_sm := hMart.stronglyMeasurable T
    exact h_sm.measurable.mono (Filt.le T) le_rfl
  have hMy_meas : ∀ j : Fin d, Measurable (My j) := by
    intro j
    obtain ⟨Filt, hMart⟩ := LevyStochCalc.Brownian.Ito.martingale_stochasticIntegral
      (W.W j) ℱ (hℱW j) (fun ω' s => coeffs.σ s (Y s ω') i j)
      (h_σ_meas_Y i j) (h_σ_progMeas_Y i j) (h_σ_sq_Y i j)
    have h_sm := hMart.stronglyMeasurable T
    exact h_sm.measurable.mono (Filt.le T) le_rfl
  -- Step 1: unfold picardStep_diffusion to ∑ j (Mx j - My j).
  have h_unfold : ∀ ω : Ω,
      LevyStochCalc.Ito.Picard.picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X T ω i
        - LevyStochCalc.Ito.Picard.picardStep_diffusion W ℱ hℱW coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y T ω i
        = ∑ j : Fin d, (Mx j ω - My j ω) := by
    intro ω
    simp only [LevyStochCalc.Ito.Picard.picardStep_diffusion,
      LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral,
      Mx, My]
    exact (Finset.sum_sub_distrib _ _).symm
  -- Step 2: rewrite the LHS using h_unfold via lintegral_congr.
  have h_LHS_rewrite :
      ∫⁻ ω, (‖LevyStochCalc.Ito.Picard.picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X T ω i
            - LevyStochCalc.Ito.Picard.picardStep_diffusion W ℱ hℱW coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y T ω i‖₊
            : ℝ≥0∞) ^ 2 ∂P
        = ∫⁻ ω, (‖∑ j : Fin d, (Mx j ω - My j ω)‖₊ : ℝ≥0∞) ^ 2 ∂P :=
    lintegral_congr (fun ω => by rw [h_unfold ω])
  rw [h_LHS_rewrite]
  -- Step 3: apply the CS-lintegral bound to M_j := Mx j - My j.
  have hM_sub_meas : ∀ j : Fin d, Measurable (fun ω => Mx j ω - My j ω) :=
    fun j => (hMx_meas j).sub (hMy_meas j)
  have h_cs := _root_.Prove2MeSourceProof.h_1a2c983c4a1fa7387543aefa
    (P := P) (d := d) (M := fun j ω => Mx j ω - My j ω) hM_sub_meas
  -- Step 4: apply isometry on each j.
  --   ∫⁻ ‖Mx j - My j‖² = ∫⁻ ∫⁻ ‖σ(X) - σ(Y)‖².
  have h_isom_j : ∀ j : Fin d,
      ∫⁻ ω, (‖Mx j ω - My j ω‖₊ : ℝ≥0∞) ^ 2 ∂P =
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (X s ω) i j - coeffs.σ s (Y s ω) i j‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P := by
    intro j
    simp only [Mx, My]
    exact LevyStochCalc.Brownian.Ito.itoIsometry_diff_brownian
      (W.W j) ℱ (hℱW j) (fun ω' s => coeffs.σ s (X s ω') i j)
      (fun ω' s => coeffs.σ s (Y s ω') i j)
      (h_σ_meas_X i j) (h_σ_meas_Y i j)
      (h_σ_progMeas_X i j) (h_σ_progMeas_Y i j)
      (h_σ_sq_X i j) (h_σ_sq_Y i j) T hT
  -- Step 5: swap ∑_j and ∫⁻ ∫⁻ on the bound.
  --   ∑_j ∫⁻ ω ∫⁻ s f_j = ∫⁻ ω ∫⁻ s ∑_j f_j.
  have h_swap : (∑ j : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (X s ω) i j - coeffs.σ s (Y s ω) i j‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P)
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        ∑ j : Fin d,
          (‖coeffs.σ s (X s ω) i j - coeffs.σ s (Y s ω) i j‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P := by
    rw [← MeasureTheory.lintegral_finsetSum]
    · refine MeasureTheory.lintegral_congr (fun ω => ?_)
      rw [← MeasureTheory.lintegral_finsetSum]
      intro j _
      have h_X := h_σ_meas_X i j
      have h_Y := h_σ_meas_Y i j
      have h_X_at_ω : Measurable (fun s : ℝ => coeffs.σ s (X s ω) i j) := by
        have h_pair_meas : Measurable (fun s : ℝ => (ω, s)) :=
          (measurable_const).prodMk measurable_id
        exact h_X.comp h_pair_meas
      have h_Y_at_ω : Measurable (fun s : ℝ => coeffs.σ s (Y s ω) i j) := by
        have h_pair_meas : Measurable (fun s : ℝ => (ω, s)) :=
          (measurable_const).prodMk measurable_id
        exact h_Y.comp h_pair_meas
      have h_sub_at_ω : Measurable
          (fun s : ℝ => coeffs.σ s (X s ω) i j - coeffs.σ s (Y s ω) i j) :=
        h_X_at_ω.sub h_Y_at_ω
      exact (h_sub_at_ω.enorm).pow_const 2
    · intro j _
      have h_X := h_σ_meas_X i j
      have h_Y := h_σ_meas_Y i j
      have h_sub : Measurable
          (fun p : Ω × ℝ =>
            coeffs.σ p.2 (X p.2 p.1) i j - coeffs.σ p.2 (Y p.2 p.1) i j) :=
        h_X.sub h_Y
      have h_meas_pow : Measurable
          (fun p : Ω × ℝ =>
            (‖coeffs.σ p.2 (X p.2 p.1) i j - coeffs.σ p.2 (Y p.2 p.1) i j‖₊
              : ℝ≥0∞) ^ 2) :=
        (h_sub.enorm).pow_const 2
      exact h_meas_pow.lintegral_prod_right
  -- Step 6: pointwise Lipschitz bound after the swap.
  --   ∑_j (σ(X) i j - σ(Y) i j)² ≤ ∑_{i' j'} (σ(X) i' j' - σ(Y) i' j')²
  --                              ≤ L_σ² ‖X-Y‖²
  have h_lip_pt : ∀ ω : Ω, ∀ s : ℝ,
      (∑ j : Fin d,
        (‖coeffs.σ s (X s ω) i j - coeffs.σ s (Y s ω) i j‖₊ : ℝ≥0∞) ^ 2)
      ≤ ENNReal.ofReal (L_σ ^ 2 * ‖X s ω - Y s ω‖ ^ 2) := by
    intro ω s
    have h_ofReal_each : ∀ j : Fin d,
        (‖coeffs.σ s (X s ω) i j - coeffs.σ s (Y s ω) i j‖₊ : ℝ≥0∞) ^ 2
          = ENNReal.ofReal ((coeffs.σ s (X s ω) i j - coeffs.σ s (Y s ω) i j) ^ 2) :=
      fun j => LevyStochCalc.Ito.Picard.ennreal_nnnorm_sq_real _
    rw [show ∑ j : Fin d,
          (‖coeffs.σ s (X s ω) i j - coeffs.σ s (Y s ω) i j‖₊ : ℝ≥0∞) ^ 2
        = ∑ j : Fin d,
            ENNReal.ofReal
              ((coeffs.σ s (X s ω) i j - coeffs.σ s (Y s ω) i j) ^ 2) from
      Finset.sum_congr rfl (fun j _ => h_ofReal_each j)]
    have h_each_nn : ∀ j : Fin d,
        (0 : ℝ) ≤ (coeffs.σ s (X s ω) i j - coeffs.σ s (Y s ω) i j) ^ 2 :=
      fun j => sq_nonneg _
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => h_each_nn j)]
    refine ENNReal.ofReal_le_ofReal ?_
    refine le_trans ?_ (h_σ_lip s (X s ω) (Y s ω))
    refine Finset.single_le_sum (f := fun i' => ∑ j : Fin d,
        (coeffs.σ s (X s ω) i' j - coeffs.σ s (Y s ω) i' j) ^ 2)
      (fun i' _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
      (Finset.mem_univ i)
  -- Step 7: chain everything.
  calc ∫⁻ ω, (‖∑ j : Fin d, (Mx j ω - My j ω)‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ (d : ℝ≥0∞) * ∑ j : Fin d,
          ∫⁻ ω, (‖Mx j ω - My j ω‖₊ : ℝ≥0∞) ^ 2 ∂P := h_cs
    _ = (d : ℝ≥0∞) * ∑ j : Fin d,
          ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖coeffs.σ s (X s ω) i j - coeffs.σ s (Y s ω) i j‖₊ : ℝ≥0∞) ^ 2
            ∂volume ∂P := by
        congr 1
        exact Finset.sum_congr rfl (fun j _ => h_isom_j j)
    _ = (d : ℝ≥0∞) * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          ∑ j : Fin d,
            (‖coeffs.σ s (X s ω) i j - coeffs.σ s (Y s ω) i j‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P := by rw [h_swap]
    _ ≤ (d : ℝ≥0∞) * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          ENNReal.ofReal (L_σ ^ 2 * ‖X s ω - Y s ω‖ ^ 2) ∂volume ∂P := by
        refine mul_le_mul_of_nonneg_left ?_ (by exact bot_le)
        refine lintegral_mono (fun ω => ?_)
        refine lintegral_mono (fun s => ?_)
        exact h_lip_pt ω s
    _ = (d : ℝ≥0∞) * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          ENNReal.ofReal (L_σ ^ 2) *
          (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
        congr 1
        refine lintegral_congr (fun ω => ?_)
        refine lintegral_congr (fun s => ?_)
        rw [LevyStochCalc.Ito.Picard.ennreal_nnnorm_sq_normed (X s ω - Y s ω),
          ← ENNReal.ofReal_mul (sq_nonneg _)]
    _ = (d : ℝ≥0∞) * (ENNReal.ofReal (L_σ ^ 2) *
          ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) := by
        congr 1
        have h_inner : ∀ ω : Ω,
            ∫⁻ s in Set.Icc (0 : ℝ) T,
              ENNReal.ofReal (L_σ ^ 2) *
              (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume
            = ENNReal.ofReal (L_σ ^ 2) *
              ∫⁻ s in Set.Icc (0 : ℝ) T,
              (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
          fun ω => lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        rw [show (fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T,
              ENNReal.ofReal (L_σ ^ 2) *
              (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume)
            = (fun ω => ENNReal.ofReal (L_σ ^ 2) *
              ∫⁻ s in Set.Icc (0 : ℝ) T,
              (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume) from funext h_inner]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal ((d : ℝ) * L_σ ^ 2) *
        ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
        rw [← mul_assoc]
        congr 1
        rw [show (d : ℝ≥0∞) = ENNReal.ofReal (d : ℝ) by
          rw [ENNReal.ofReal_natCast]]
        rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (d:ℝ))]
end LevyStochCalc.Ito.Picard

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

end LevyStochCalc.Ito.Picard


