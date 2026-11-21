-- Prove2me | Definitions.Def_LevyStochCalc_Ito_PicardSelfMap_F000
-- name    : LevyStochCalc_Ito_PicardSelfMap_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:49:51.794184+00:00
-- url     : https://prove2.me/theorems/0810caf6-da49-4198-9d4b-a5942abd1292
-- title:
--   Source declarations: LevyStochCalc.Ito.PicardSelfMap
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.PicardSelfMap. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardSelfMap_F000A
import Definitions.Def_LevyStochCalc_Ito_PicardSelfMap_F000B

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- **Sub-additivity of squared sums on three terms.**

  `(a + b + c)² ≤ 3 · (a² + b² + c²)`.

This is the standard Cauchy-Schwarz / AM-QM bound on three terms and is the
load-bearing combinatorial step that turns the three component L² bounds
(drift, σ, γ) into a single bound on the full Picard step. -/
lemma sq_add_three_le (a b c : ℝ) :
    (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- **Sub-additivity of squared norms on three vector terms.**

For `u v w : Fin n → ℝ`,

  `∑ i, (u i + v i + w i)² ≤ 3 · (∑ i, (u i)² + ∑ i, (v i)² + ∑ i, (w i)²)`.

This is `sq_add_three_le` applied componentwise and summed over `Fin n`. -/
lemma sum_sq_add_three_le {n : ℕ} (u v w : Fin n → ℝ) :
    ∑ i : Fin n, (u i + v i + w i) ^ 2
      ≤ 3 * (∑ i : Fin n, (u i) ^ 2 + ∑ i : Fin n, (v i) ^ 2
              + ∑ i : Fin n, (w i) ^ 2) := by
  have h_each : ∀ i : Fin n, (u i + v i + w i) ^ 2
      ≤ 3 * ((u i) ^ 2 + (v i) ^ 2 + (w i) ^ 2) := fun i =>
    sq_add_three_le (u i) (v i) (w i)
  calc (∑ i : Fin n, (u i + v i + w i) ^ 2)
      ≤ ∑ i : Fin n, 3 * ((u i) ^ 2 + (v i) ^ 2 + (w i) ^ 2) :=
        Finset.sum_le_sum (fun i _ => h_each i)
    _ = 3 * ∑ i : Fin n, ((u i) ^ 2 + (v i) ^ 2 + (w i) ^ 2) := by
        rw [← Finset.mul_sum]
    _ = 3 * (∑ i : Fin n, (u i) ^ 2 + ∑ i : Fin n, (v i) ^ 2
              + ∑ i : Fin n, (w i) ^ 2) := by
        congr 1
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
set_option maxHeartbeats 4000000 in
-- The three Picard components are compared under one `Finset.sum` over `Fin n`;
-- `nlinarith` on the resulting sum-of-squares exceeds the default budget.
/-- **Picard step pointwise sum-of-squares triangle bound.**

For `Φ X = drift X + diff X + jump X` and any two `X Y`, the squared
Euclidean norm of `(Φ X - Φ Y) t ω` is bounded componentwise by three
times the sum of the three component squared norms:

  `∑ i, ((Φ X t ω - Φ Y t ω) i)²
    ≤ 3 · (∑ i, ((drift_diff)i)² + ∑ i, ((diff_diff)i)² + ∑ i, ((jump_diff)i)²)`.

This is the algebraic identity `picardStep = drift + diff + jump` followed
by `sum_sq_add_three_le`. -/
lemma picardStep_diff_sum_sq_le
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    {n d : ℕ}
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X Y : ℝ → Ω → (Fin n → ℝ))
    (x₀ : Fin n → ℝ)
    (h_σ_meas_X : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    (h_σ_progMeas_X : ∀ i : Fin n, ∀ j : Fin d,
        Probability.ProgressivelyMeasurable ℱ
          (fun ω s => coeffs.σ s (X s ω) i j))
    (h_σ_sq_X : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_γ_meas_X : ∀ i : Fin n,
      Measurable (fun (p : Ω × ℝ × E) => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
    (h_γ_progMeas_X : ∀ i : Fin n,
        Probability.MarkedProgressivelyMeasurable ℱ
          (fun ω s e => coeffs.γ s (X s ω) e i))
    (h_γ_sq_X : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (h_σ_meas_Y : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (Y s ω) i j)))
    (h_σ_progMeas_Y : ∀ i : Fin n, ∀ j : Fin d,
        Probability.ProgressivelyMeasurable ℱ
          (fun ω s => coeffs.σ s (Y s ω) i j))
    (h_σ_sq_Y : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (Y s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_γ_meas_Y : ∀ i : Fin n,
      Measurable (fun (p : Ω × ℝ × E) => coeffs.γ p.2.1 (Y p.2.1 p.1) p.2.2 i))
    (h_γ_progMeas_Y : ∀ i : Fin n,
        Probability.MarkedProgressivelyMeasurable ℱ
          (fun ω s e => coeffs.γ s (Y s ω) e i))
    (h_γ_sq_Y : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (Y s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (t : ℝ) (ω : Ω) :
    ∑ i : Fin n, ((picardStep W N ℱ hℱW hℱN coeffs X x₀
        h_σ_meas_X h_σ_progMeas_X h_σ_sq_X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
      - picardStep W N ℱ hℱW hℱN coeffs Y x₀
        h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2
    ≤ 3 * (∑ i : Fin n, ((picardStep_drift coeffs X x₀ t ω
                          - picardStep_drift coeffs Y x₀ t ω) i) ^ 2
          + ∑ i : Fin n, ((picardStep_diffusion W ℱ hℱW coeffs X
                            h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
                          - picardStep_diffusion W ℱ hℱW coeffs Y
                            h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2
          + ∑ i : Fin n, ((picardStep_jump N ℱ hℱN coeffs X
                            h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
                          - picardStep_jump N ℱ hℱN coeffs Y
                            h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2) := by
  -- Unfold picardStep = drift + diffusion + jump and apply sum_sq_add_three_le.
  unfold picardStep
  have h_sq_eq : ∀ i : Fin n,
      (((picardStep_drift coeffs X x₀ t ω
            + picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
            + picardStep_jump N ℱ hℱN coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω)
          - (picardStep_drift coeffs Y x₀ t ω
            + picardStep_diffusion W ℱ hℱW coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω
            + picardStep_jump N ℱ hℱN coeffs Y h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω)) i) ^ 2
      = ((picardStep_drift coeffs X x₀ t ω - picardStep_drift coeffs Y x₀ t ω) i
          + (picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
              - picardStep_diffusion W ℱ hℱW coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i
          + (picardStep_jump N ℱ hℱN coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
              - picardStep_jump N ℱ hℱN coeffs Y
                  h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2 := by
    intro i
    simp only [Pi.add_apply, Pi.sub_apply]; ring
  rw [Finset.sum_congr rfl (fun i _ => h_sq_eq i)]
  exact sum_sq_add_three_le _ _ _
end LevyStochCalc.Ito.Picard


