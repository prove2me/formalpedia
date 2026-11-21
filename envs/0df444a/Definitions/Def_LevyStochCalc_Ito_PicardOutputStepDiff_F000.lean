-- Prove2me | Definitions.Def_LevyStochCalc_Ito_PicardOutputStepDiff_F000
-- name    : LevyStochCalc_Ito_PicardOutputStepDiff_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:54:30.004521+00:00
-- url     : https://prove2.me/theorems/00b17695-8673-44bf-82e3-1b70047a582c
-- title:
--   Source declarations: LevyStochCalc.Ito.PicardOutputStepDiff
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.PicardOutputStepDiff. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardOutputWeighting_F000
import Definitions.Def_LevyStochCalc_Ito_PicardOutputWeighting_F002
import Definitions.Def_LevyStochCalc_Ito_PicardOutputWeighting_F003
import Definitions.Def_SourceProof_afc5c99feb5115695a5f6b39

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

omit [MeasurableSpace E] [MeasureTheory.IsProbabilityMeasure P] in
/-- **Combining three per-time bounds with a common right-hand side.** For a process that splits
as a sum of three, `‖a + b + c‖² ≤ 3(‖a‖² + ‖b‖² + ‖c‖²)` turns three separate second-moment
bounds into one, with the constants added and tripled. -/
theorem lintegral_sq_sum3_le {U₁ U₂ U₃ : Ω → (Fin n → ℝ)} {c₁ c₂ c₃ R : ℝ≥0∞}
    (hm₁ : ∀ i : Fin n, Measurable fun ω => (‖U₁ ω i‖₊ : ℝ≥0∞) ^ 2)
    (hm₂ : ∀ i : Fin n, Measurable fun ω => (‖U₂ ω i‖₊ : ℝ≥0∞) ^ 2)
    (hm₃ : ∀ i : Fin n, Measurable fun ω => (‖U₃ ω i‖₊ : ℝ≥0∞) ^ 2)
    (h₁ : ∫⁻ ω, ∑ i, (‖U₁ ω i‖₊ : ℝ≥0∞) ^ 2 ∂P ≤ c₁ * R)
    (h₂ : ∫⁻ ω, ∑ i, (‖U₂ ω i‖₊ : ℝ≥0∞) ^ 2 ∂P ≤ c₂ * R)
    (h₃ : ∫⁻ ω, ∑ i, (‖U₃ ω i‖₊ : ℝ≥0∞) ^ 2 ∂P ≤ c₃ * R) :
    ∫⁻ ω, ∑ i, (‖U₁ ω i + U₂ ω i + U₃ ω i‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ 3 * (c₁ + c₂ + c₃) * R := by
  have hM₁ : Measurable fun ω => ∑ i, (‖U₁ ω i‖₊ : ℝ≥0∞) ^ 2 :=
    Finset.measurable_sum _ fun i _ => hm₁ i
  have hM₂ : Measurable fun ω => ∑ i, (‖U₂ ω i‖₊ : ℝ≥0∞) ^ 2 :=
    Finset.measurable_sum _ fun i _ => hm₂ i
  have hM₃ : Measurable fun ω => ∑ i, (‖U₃ ω i‖₊ : ℝ≥0∞) ^ 2 :=
    Finset.measurable_sum _ fun i _ => hm₃ i
  have hsum : ∀ ω : Ω, ∑ i, (‖U₁ ω i + U₂ ω i + U₃ ω i‖₊ : ℝ≥0∞) ^ 2
      ≤ 3 * (∑ i, (‖U₁ ω i‖₊ : ℝ≥0∞) ^ 2) + 3 * (∑ i, (‖U₂ ω i‖₊ : ℝ≥0∞) ^ 2)
        + 3 * (∑ i, (‖U₃ ω i‖₊ : ℝ≥0∞) ^ 2) := by
    intro ω
    refine le_trans (Finset.sum_le_sum fun i _ => _root_.Prove2MeSourceProof.h_afc5c99feb5115695a5f6b39 _ _ _) (le_of_eq ?_)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum,
      Finset.mul_sum]
  have hM1' : Measurable fun ω : Ω => 3 * (∑ i, (‖U₁ ω i‖₊ : ℝ≥0∞) ^ 2) := hM₁.const_mul 3
  have hM2' : Measurable fun ω : Ω => 3 * (∑ i, (‖U₂ ω i‖₊ : ℝ≥0∞) ^ 2) := hM₂.const_mul 3
  have hM12 : Measurable fun ω : Ω =>
      3 * (∑ i, (‖U₁ ω i‖₊ : ℝ≥0∞) ^ 2) + 3 * (∑ i, (‖U₂ ω i‖₊ : ℝ≥0∞) ^ 2) := hM1'.add hM2'
  refine (lintegral_mono hsum).trans ?_
  rw [MeasureTheory.lintegral_add_left hM12,
    MeasureTheory.lintegral_add_left hM1',
    MeasureTheory.lintegral_const_mul' _ _ (by simp : (3 : ℝ≥0∞) ≠ ⊤),
    MeasureTheory.lintegral_const_mul' _ _ (by simp : (3 : ℝ≥0∞) ≠ ⊤),
    MeasureTheory.lintegral_const_mul' _ _ (by simp : (3 : ℝ≥0∞) ≠ ⊤)]
  calc 3 * (∫⁻ ω, ∑ i, (‖U₁ ω i‖₊ : ℝ≥0∞) ^ 2 ∂P)
        + 3 * (∫⁻ ω, ∑ i, (‖U₂ ω i‖₊ : ℝ≥0∞) ^ 2 ∂P)
        + 3 * (∫⁻ ω, ∑ i, (‖U₃ ω i‖₊ : ℝ≥0∞) ^ 2 ∂P)
      ≤ 3 * (c₁ * R) + 3 * (c₂ * R) + 3 * (c₃ * R) :=
        add_le_add (add_le_add (mul_le_mul' le_rfl h₁) (mul_le_mul' le_rfl h₂))
          (mul_le_mul' le_rfl h₃)
    _ = 3 * (c₁ + c₂ + c₃) * R := by ring
omit [MeasurableSpace Ω] [MeasureTheory.IsProbabilityMeasure P] in
/-- The `μ` clause of `IsLipschitz`, read on a single coordinate. -/
theorem mu_lip_componentwise {ν : MeasureTheory.Measure E}
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E) {L : ℝ}
    (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (s : ℝ) (x₁ x₂ : Fin n → ℝ) (i : Fin n) :
    |coeffs.μ s x₁ i - coeffs.μ s x₂ i| ≤ L * ‖x₁ - x₂‖ := by
  refine le_trans ?_ (hLip.2.1 s x₁ x₂)
  simpa [Real.norm_eq_abs, Pi.sub_apply] using
    norm_le_pi_norm (coeffs.μ s x₁ - coeffs.μ s x₂) i
omit [MeasurableSpace E] [MeasureTheory.IsProbabilityMeasure P] in
/-- The two shapes of the coordinate second moment agree. -/
theorem lintegral_ofReal_sum_sq_eq (U : Ω → (Fin n → ℝ)) :
    ∫⁻ ω, ENNReal.ofReal (∑ i, (U ω i) ^ 2) ∂P
      = ∫⁻ ω, ∑ i, (‖U ω i‖₊ : ℝ≥0∞) ^ 2 ∂P := by
  refine lintegral_congr fun ω => ?_
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
  exact (Finset.sum_congr rfl fun i _ => sq_coe_nnnorm_real (U ω i)).symm
/-- The Picard step is the sum of its three components, coordinatewise. -/
theorem picardStep_apply_eq
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ)) (x₀ : Fin n → ℝ)
    (h_σ_meas : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    (h_σ_progMeas : ∀ i : Fin n, ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (X s ω) i j))
    (h_σ_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_γ_meas : ∀ i : Fin n,
      Measurable (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
    (h_γ_progMeas : ∀ i : Fin n,
      Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (X s ω) e i))
    (h_γ_sq : ∀ i : Fin n, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (t : ℝ) (ω : Ω) (i : Fin n) :
    picardStep W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas h_σ_progMeas h_σ_sq
        h_γ_meas h_γ_progMeas h_γ_sq t ω i
      = picardStep_drift coeffs X x₀ t ω i
        + picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq t ω i
        + picardStep_jump N ℱ hℱN coeffs X h_γ_meas h_γ_progMeas h_γ_sq t ω i := rfl
-- `picardStep` and the two stochastic-integral components unfold to `Finset` sums over `Fin d`
-- and to the `L²`-limit integrals; the statement below repeats those terms verbatim on both
-- sides, so unfolding them during unification only costs time. Sealed as in `Ito/Picard.lean`.
attribute [local irreducible] picardStep picardStep_diffusion picardStep_jump
attribute [local irreducible]
  LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral
attribute [local irreducible] LevyStochCalc.Brownian.Ito.stochasticIntegral

end Weighting

end LevyStochCalc.Ito.Picard


