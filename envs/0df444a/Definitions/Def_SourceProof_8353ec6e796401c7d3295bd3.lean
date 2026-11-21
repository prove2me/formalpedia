-- Prove2me | Definitions.Def_SourceProof_8353ec6e796401c7d3295bd3
-- name    : SourceProof_8353ec6e796401c7d3295bd3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:46:58.255053+00:00
-- url     : https://prove2.me/theorems/b1a6dc2e-98a7-40db-970b-02e3d5520f12
-- title:
--   LevyStochCalc source module: SourceProof_8353ec6e796401c7d3295bd3
-- statement:
--   The original source theorem `LevyStochCalc.Ito.Picard.jump_diff_lintegral_sq_bound` comes from the `LevyStochCalc.Ito.PicardOutputWeighting` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardOutputWeighting_F003
import Definitions.Def_SourceProof_7d42b3f858f0e2725802728a

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


theorem _root_.Prove2MeSourceProof.h_8353ec6e796401c7d3295bd3 {ν : MeasureTheory.Measure E}
    [MeasureTheory.SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (X Y : ℝ → Ω → (Fin n → ℝ))
    (hX_meas : ∀ i : Fin n,
      Measurable (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
    (hX_progMeas : ∀ i : Fin n,
      Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (X s ω) e i))
    (hX_sq : ∀ i : Fin n, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hY_meas : ∀ i : Fin n,
      Measurable (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (Y p.2.1 p.1) p.2.2 i))
    (hY_progMeas : ∀ i : Fin n,
      Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (Y s ω) e i))
    (hY_sq : ∀ i : Fin n, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖coeffs.γ s (Y s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t) :
    ∫⁻ ω, ∑ i : Fin n,
        (‖picardStep_jump N ℱ hℱN coeffs X hX_meas hX_progMeas hX_sq t ω i
          - picardStep_jump N ℱ hℱN coeffs Y hY_meas hY_progMeas hY_sq t ω i‖₊
          : ℝ≥0∞) ^ 2 ∂P
      ≤ ENNReal.ofReal ((n : ℝ) * L ^ 2)
          * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
              (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  have hmeas : ∀ i : Fin n, Measurable fun ω =>
      (‖LevyStochCalc.Ito.Picard.picardStep_jump N ℱ hℱN coeffs X hX_meas hX_progMeas hX_sq t ω i
        - LevyStochCalc.Ito.Picard.picardStep_jump N ℱ hℱN coeffs Y hY_meas hY_progMeas hY_sq t ω i‖₊ : ℝ≥0∞) ^ 2 :=
    fun i =>
      ((((LevyStochCalc.Ito.Picard.measurable_picardStep_jump N ℱ hℱN coeffs X hX_meas hX_progMeas hX_sq i t).sub
        (LevyStochCalc.Ito.Picard.measurable_picardStep_jump N ℱ hℱN coeffs Y hY_meas hY_progMeas hY_sq i
          t)).nnnorm).coe_nnreal_ennreal).pow_const 2
  rw [MeasureTheory.lintegral_finsetSum _ fun i _ => hmeas i]
  calc ∑ i : Fin n, ∫⁻ ω,
        (‖LevyStochCalc.Ito.Picard.picardStep_jump N ℱ hℱN coeffs X hX_meas hX_progMeas hX_sq t ω i
          - LevyStochCalc.Ito.Picard.picardStep_jump N ℱ hℱN coeffs Y hY_meas hY_progMeas hY_sq t ω i‖₊
          : ℝ≥0∞) ^ 2 ∂P
      ≤ ∑ _i : Fin n, ENNReal.ofReal (L ^ 2)
          * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
              (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
        Finset.sum_le_sum fun i _ =>
          _root_.Prove2MeSourceProof.h_7d42b3f858f0e2725802728a N ℱ hℱN coeffs hLip.1 X Y i
            (LevyStochCalc.Ito.Picard.gamma_lip_componentwise coeffs hLip X Y i)
            hX_meas hX_progMeas hX_sq hY_meas hY_progMeas hY_sq t ht
    _ = ENNReal.ofReal ((n : ℝ) * L ^ 2)
          * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
              (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg n), ← mul_assoc]
        congr 2
        simp
end Weighting

end LevyStochCalc.Ito.Picard


