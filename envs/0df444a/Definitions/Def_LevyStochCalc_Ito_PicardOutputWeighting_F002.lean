-- Prove2me | Definitions.Def_LevyStochCalc_Ito_PicardOutputWeighting_F002
-- name    : LevyStochCalc_Ito_PicardOutputWeighting_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:52:20.131177+00:00
-- url     : https://prove2.me/theorems/1fcc35e6-bca2-4125-87b6-e7cdbd0e32a8
-- title:
--   Source declarations: LevyStochCalc.Ito.PicardOutputWeighting
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.PicardOutputWeighting. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardOutputWeighting_F001
import Definitions.Def_SourceProof_1fbaca62d40510f967b3ca0a
import Definitions.Def_SourceProof_c06333d6fb82799a96874046
import Definitions.Def_SourceProof_e319076aff1b47a860ce2705

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

omit [MeasurableSpace E] [MeasureTheory.IsProbabilityMeasure P] in
/-- The supremum norm is dominated by the coordinate sum, in `ℝ≥0∞`. -/
theorem sq_coe_nnnorm_le_sum (v : Fin n → ℝ) :
    (‖v‖₊ : ℝ≥0∞) ^ 2 ≤ ∑ i, (‖v i‖₊ : ℝ≥0∞) ^ 2 :=
  (sq_coe_nnnorm v).le.trans (ofReal_sq_norm_le_sum v)
omit [MeasurableSpace E] in
/-- `bieleckiNorm_le_of_perTime` with the window energy measured in the supremum norm, which is
the form the per-component difference estimates of `Ito/Picard.lean` produce. -/
theorem bieleckiNorm_le_of_perTime_sup {β : ℝ} (hβ : 0 < β) {T C : ℝ} (hC : 0 ≤ C)
    (U Z : ℝ → Ω → (Fin n → ℝ))
    (hZ : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => Z s ω))
    (hbd : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫⁻ ω, ENNReal.ofReal (∑ i, (U t ω i) ^ 2) ∂P
        ≤ ENNReal.ofReal C
            * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
                (‖Z s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) :
    bieleckiNorm (P := P) β T U
      ≤ (ENNReal.ofReal (C / (2 * β))) ^ ((1 : ℝ) / 2) * bieleckiNorm (P := P) β T Z :=
  _root_.Prove2MeSourceProof.h_1fbaca62d40510f967b3ca0a hβ hC U Z hZ fun t ht =>
    (hbd t ht).trans (mul_le_mul' le_rfl
      (lintegral_mono fun ω => lintegral_mono fun s => sq_coe_nnnorm_le_sum (Z s ω)))
omit [MeasurableSpace E] in
/-- `bieleckiNorm_le_of_perTime` with the window energy as a Bochner integral. -/
theorem bieleckiNorm_le_of_perTime_bochner {β : ℝ} (hβ : 0 < β) {T C : ℝ} (hC : 0 ≤ C)
    (U Z : ℝ → Ω → (Fin n → ℝ))
    (hZ : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => Z s ω))
    (hbd : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫⁻ ω, ENNReal.ofReal (∑ i, (U t ω i) ^ 2) ∂P
        ≤ ENNReal.ofReal C
            * ∫⁻ ω, ENNReal.ofReal (∫ s in Set.Icc (0 : ℝ) t, ‖Z s ω‖ ^ 2 ∂volume) ∂P) :
    bieleckiNorm (P := P) β T U
      ≤ (ENNReal.ofReal (C / (2 * β))) ^ ((1 : ℝ) / 2) * bieleckiNorm (P := P) β T Z :=
  _root_.Prove2MeSourceProof.h_1fbaca62d40510f967b3ca0a hβ hC U Z hZ fun t ht =>
    (hbd t ht).trans (mul_le_mul' le_rfl
      (lintegral_mono fun ω => lintegral_window_norm_le_sum t ω))
omit [MeasurableSpace E] [MeasureTheory.IsProbabilityMeasure P] in
/-- **The drift half of the per-time contraction estimate.** The per-component bound of
`picardStep_drift_diff_lipschitz_sq_componentwise` needs four integrability facts about the
path; local finiteness of the energies supplies all of them off one null set. -/
theorem ae_drift_diff_sq_bound
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    {L_μ : ℝ} (hL_μ_nn : 0 ≤ L_μ)
    (h_μ_lip : ∀ s : ℝ, ∀ x₁ x₂ : Fin n → ℝ, ∀ i : Fin n,
      |coeffs.μ s x₁ i - coeffs.μ s x₂ i| ≤ L_μ * ‖x₁ - x₂‖)
    (X Y : ℝ → Ω → (Fin n → ℝ)) (x₀ : Fin n → ℝ)
    (hμX : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X s ω) i))
    (hμY : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (Y s ω) i))
    (hXYm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => ‖X s ω - Y s ω‖))
    (hμXsq : ∀ i : Fin n, ∀ b : ℝ, 0 < b → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hμYsq : ∀ i : Fin n, ∀ b : ℝ, 0 < b → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      (‖coeffs.μ s (Y s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hXYsq : ∀ b : ℝ, 0 < b → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ ω ∂P, ∑ i : Fin n,
        ((picardStep_drift coeffs X x₀ t ω - picardStep_drift coeffs Y x₀ t ω) i) ^ 2
      ≤ (n : ℝ) * L_μ ^ 2 * t * ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2 ∂volume := by
  have hXYsq' : ∀ b : ℝ, 0 < b → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      (‖(‖X s ω - Y s ω‖ : ℝ)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
    intro b hb
    refine lt_of_le_of_lt (le_of_eq ?_) (hXYsq b hb)
    exact lintegral_congr fun ω => lintegral_congr fun s => by rw [nnnorm_norm]
  filter_upwards [MeasureTheory.ae_all_iff.mpr fun i : Fin n =>
      ae_integrableOn_of_lintegral_sq (hμX i) (hμXsq i),
    MeasureTheory.ae_all_iff.mpr fun i : Fin n =>
      ae_integrableOn_of_lintegral_sq (hμY i) (hμYsq i),
    ae_integrableOn_of_lintegral_sq hXYm hXYsq',
    _root_.Prove2MeSourceProof.h_f512774c3d012a8b87c44ec5 hXYm hXYsq'] with ω hX hY hXY hXYL2
  calc ∑ i : Fin n,
        ((picardStep_drift coeffs X x₀ t ω - picardStep_drift coeffs Y x₀ t ω) i) ^ 2
      ≤ ∑ _i : Fin n, L_μ ^ 2 * t
          * ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2 ∂volume :=
        Finset.sum_le_sum fun i _ =>
          _root_.Prove2MeSourceProof.h_c06333d6fb82799a96874046 coeffs hL_μ_nn h_μ_lip X Y x₀ t ht
            ω i (hX i t) (hY i t) (hXY t) (hXYL2 t)
    _ = (n : ℝ) * L_μ ^ 2 * t
          * ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2 ∂volume := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
omit [MeasurableSpace E] in
/-- **The drift half of the per-time contraction estimate, in lower-integral form.**
`picardStep_drift_diff_lintegral_sq_bound` with both of its almost-everywhere hypotheses
discharged. -/
theorem drift_diff_lintegral_sq_bound
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    {L_μ : ℝ} (hL_μ_nn : 0 ≤ L_μ)
    (h_μ_lip : ∀ s : ℝ, ∀ x₁ x₂ : Fin n → ℝ, ∀ i : Fin n,
      |coeffs.μ s x₁ i - coeffs.μ s x₂ i| ≤ L_μ * ‖x₁ - x₂‖)
    (X Y : ℝ → Ω → (Fin n → ℝ)) (x₀ : Fin n → ℝ)
    (hμX : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X s ω) i))
    (hμY : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (Y s ω) i))
    (hXYm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => ‖X s ω - Y s ω‖))
    (hμXsq : ∀ i : Fin n, ∀ b : ℝ, 0 < b → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hμYsq : ∀ i : Fin n, ∀ b : ℝ, 0 < b → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      (‖coeffs.μ s (Y s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hXYsq : ∀ b : ℝ, 0 < b → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ ω, ENNReal.ofReal (∑ i : Fin n,
        ((picardStep_drift (E := E) coeffs X x₀ t ω
            - picardStep_drift coeffs Y x₀ t ω) i) ^ 2) ∂P
      ≤ ENNReal.ofReal ((n : ℝ) * L_μ ^ 2 * t)
          * ∫⁻ ω, ENNReal.ofReal
              (∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2) ∂P :=
  _root_.Prove2MeSourceProof.h_e319076aff1b47a860ce2705 P coeffs hL_μ_nn h_μ_lip X Y x₀ t ht
    (ae_drift_diff_sq_bound coeffs hL_μ_nn h_μ_lip X Y x₀ hμX hμY hXYm hμXsq hμYsq hXYsq ht)
    (Filter.Eventually.of_forall fun _ =>
      MeasureTheory.integral_nonneg_of_ae (Filter.Eventually.of_forall fun _ => by positivity))
end Weighting

end LevyStochCalc.Ito.Picard


