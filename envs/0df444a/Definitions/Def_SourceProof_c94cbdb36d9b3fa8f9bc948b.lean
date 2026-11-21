-- Prove2me | Definitions.Def_SourceProof_c94cbdb36d9b3fa8f9bc948b
-- name    : SourceProof_c94cbdb36d9b3fa8f9bc948b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T22:03:56.117902+00:00
-- url     : https://prove2.me/theorems/d277e015-444d-4090-814c-8b4d44b32b78
-- title:
--   LevyStochCalc source module: SourceProof_c94cbdb36d9b3fa8f9bc948b
-- statement:
--   The original source theorem `LevyStochCalc.Ito.Picard.bieleckiNorm_picardStep_diff_le` comes from the `LevyStochCalc.Ito.PicardOutputStepDiff` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_217f44132bf28379085aa30a
import Definitions.Def_SourceProof_48104e2f7ef90350b5eb61e7

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
-- Same reason as `lintegral_sq_picardStep_diff_le`: the statement names the full Picard term
-- twice, once along each path.

theorem _root_.Prove2MeSourceProof.h_c94cbdb36d9b3fa8f9bc948b
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
    (hZm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => X s ω - Y s ω))
    {β : ℝ} (hβ : 0 < β) {T : ℝ} (hT : 0 < T) :
    bieleckiNorm (P := P) β T (fun t ω i =>
        picardStep W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas_X h_σ_progMeas_X h_σ_sq_X
            h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω i
          - picardStep W N ℱ hℱW hℱN coeffs Y x₀ h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y
              h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω i)
      ≤ (ENNReal.ofReal
            ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
              / (2 * β))) ^ ((1 : ℝ) / 2)
        * bieleckiNorm (P := P) β T (fun t ω i => X t ω i - Y t ω i) := by
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hdn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hCnn : (0 : ℝ)
      ≤ 3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2) := by
    have h1 : (0 : ℝ) ≤ (n : ℝ) * L ^ 2 * T := by positivity
    have h2 : (0 : ℝ) ≤ (n : ℝ) * ((d : ℝ) * L ^ 2) := by positivity
    have h3 : (0 : ℝ) ≤ (n : ℝ) * L ^ 2 := by positivity
    linarith
  refine _root_.Prove2MeSourceProof.h_1fbaca62d40510f967b3ca0a hβ hCnn _ _ hZm fun t ht => ?_
  rw [LevyStochCalc.Ito.Picard.lintegral_ofReal_sum_sq_eq]
  rcases ht.1.lt_or_eq with ht0 | ht0
  · refine (_root_.Prove2MeSourceProof.h_48104e2f7ef90350b5eb61e7 W N ℱ hℱW hℱN coeffs hLip X Y x₀
      h_σ_meas_X h_σ_progMeas_X h_σ_sq_X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X
      h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y
      hμX hμY hXYm hμXsq hμYsq hXYsq ht0).trans (mul_le_mul' ?_ le_rfl)
    have hstep : ENNReal.ofReal ((n : ℝ) * L ^ 2 * t)
        ≤ ENNReal.ofReal ((n : ℝ) * L ^ 2 * T) := by
      refine ENNReal.ofReal_le_ofReal ?_
      have : (0 : ℝ) ≤ (n : ℝ) * L ^ 2 := by positivity
      nlinarith [ht.2, this]
    calc 3 * (ENNReal.ofReal ((n : ℝ) * L ^ 2 * t)
            + ENNReal.ofReal ((n : ℝ) * ((d : ℝ) * L ^ 2)) + ENNReal.ofReal ((n : ℝ) * L ^ 2))
        ≤ 3 * (ENNReal.ofReal ((n : ℝ) * L ^ 2 * T)
            + ENNReal.ofReal ((n : ℝ) * ((d : ℝ) * L ^ 2)) + ENNReal.ofReal ((n : ℝ) * L ^ 2)) :=
          mul_le_mul' le_rfl (add_le_add (add_le_add hstep le_rfl) le_rfl)
      _ = ENNReal.ofReal
            (3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2)) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
            ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_ofNat]
  · have hzero : ∀ᵐ ω ∂P, ∑ i : Fin n,
        (‖LevyStochCalc.Ito.Picard.picardStep W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas_X h_σ_progMeas_X h_σ_sq_X
              h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω i
            - LevyStochCalc.Ito.Picard.picardStep W N ℱ hℱW hℱN coeffs Y x₀ h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y
                h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω i‖₊ : ℝ≥0∞) ^ 2 = 0 := by
      filter_upwards [_root_.Prove2MeSourceProof.h_217f44132bf28379085aa30a W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas_X h_σ_progMeas_X
          h_σ_sq_X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X,
        _root_.Prove2MeSourceProof.h_217f44132bf28379085aa30a W N ℱ hℱW hℱN coeffs Y x₀ h_σ_meas_Y h_σ_progMeas_Y
          h_σ_sq_Y h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y] with ω hX hY
      simp [← ht0, hX, hY]
    rw [lintegral_congr_ae hzero, MeasureTheory.lintegral_zero]
    exact zero_le
end Weighting

end LevyStochCalc.Ito.Picard


