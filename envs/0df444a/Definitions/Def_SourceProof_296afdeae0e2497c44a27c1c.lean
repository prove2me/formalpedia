-- Prove2me | Definitions.Def_SourceProof_296afdeae0e2497c44a27c1c
-- name    : SourceProof_296afdeae0e2497c44a27c1c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:11:19.576818+00:00
-- url     : https://prove2.me/theorems/a2897ef0-79fb-4e68-91cd-d9f1873c73d3
-- title:
--   LevyStochCalc source module: SourceProof_296afdeae0e2497c44a27c1c
-- statement:
--   The original source theorem `LevyStochCalc.Examples.Nonvacuity.integral_sq_solvesOn_one` comes from the `NonvacuityItoLevyPath` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_NonvacuityItoLevyPath_F000
import Definitions.Def_SourceProof_f574d7521b7b37d4f4a7a428

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The value at time `1` of the jump diffusion `dX_t = dW_t + ∫_ℝ e Ñ(dt, de)`

For the coefficients `coeffs` (`μ = 0`, `σ = 1`, `γ(s, x, e) = e`) and the jump intensity
`δ₁`, a path solving the jump-diffusion integral equation from `0` relative to a filtration
carrying both driver properties has second moment `2` in its single coordinate at time `1`:
the drift vanishes, the Brownian leg contributes `∫_0^1 1 ds = 1`, the compensated leg
contributes `∫_0^1 ∫_ℝ e² δ₁(de) ds = 1`, and the two legs are orthogonal. In particular that
coordinate is not almost surely `0` at time `1`.

The second moment is the expectation form of the quadratic Itô formula,
`LevyStochCalc.Ito.SecondMoment.integral_mul_self_eq_of_isItoLevyProcess`, whose orthogonality
input is a cross witness for the filtration; `crossWitnessAugRightCont` carries the driver's
own witness to the augmented right-continuation of the joint filtration, the filtration at
which `LevyStochCalc.Ito.Picard.exists_globalSolution` produces a solution.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Examples.Nonvacuity

open LevyStochCalc.Driver (LevyDriver)
open LevyStochCalc.Ito.Picard (SolvesOn eqn_sum_form)
open LevyStochCalc.Ito.Setting (IsItoLevyProcess)

universe u v

/-! ### A cross witness at the augmented right-continuation -/

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-! ### The second moment of a solution at time `1` -/

section Solution

variable {D : LevyDriver P 1 jumpIntensity}
  {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin 1, Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : Poisson.IsPoissonFiltration D.N ℱ} {X : ℝ → Ω → (Fin 1 → ℝ)}


theorem _root_.Prove2MeSourceProof.h_296afdeae0e2497c44a27c1c (𝒲 : D.CrossWitness ℱ)
    (hXm : Measurable (Function.uncurry X))
    (hXsol : ∀ T : ℝ, SolvesOn D.W D.N ℱ hℱW hℱN coeffs (0 : Fin 1 → ℝ) X T) :
    ∫ ω, X 1 ω 0 * X 1 ω 0 ∂P = 2 := by
  have hbeq : (Function.uncurry fun (ω : Ω) (s : ℝ) => LevyStochCalc.Examples.Nonvacuity.coeffs.μ s (X s ω) 0)
      = fun _ : Ω × ℝ => (0 : ℝ) := rfl
  have hbm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => LevyStochCalc.Examples.Nonvacuity.coeffs.μ s (X s ω) 0) := by
    rw [hbeq]; exact measurable_const
  have hbp : Probability.ProgressivelyMeasurable ℱ
      fun (ω : Ω) (s : ℝ) => LevyStochCalc.Examples.Nonvacuity.coeffs.μ s (X s ω) 0 :=
    Brownian.Ito.progressivelyMeasurable_const ℱ 0
  have hbq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖LevyStochCalc.Examples.Nonvacuity.coeffs.μ s (X s ω) 0‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
    intro T _
    simp [LevyStochCalc.Examples.Nonvacuity.coeffs]
  have e2 : ∀ s : ℝ, ∫ ω, X s ω 0 * LevyStochCalc.Examples.Nonvacuity.coeffs.μ s (X s ω) 0 ∂P = 0 := by
    intro s
    simp [coeffs_mu_apply]
  have e3 : ∀ j : Fin 1, (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) 1,
      (‖LevyStochCalc.Examples.Nonvacuity.coeffs.σ s (X s ω) 0 j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) = 1 := by
    intro j
    have hpt : ∀ (ω : Ω) (s : ℝ), (‖LevyStochCalc.Examples.Nonvacuity.coeffs.σ s (X s ω) 0 j‖₊ : ℝ≥0∞) ^ 2 = 1 := by
      intro ω s
      rw [LevyStochCalc.Examples.Nonvacuity.coeffs_sigma_apply]
      simp
    simp only [hpt, lintegral_const, measure_univ, mul_one, Measure.restrict_apply_univ,
      Real.volume_Icc, sub_zero, ENNReal.ofReal_one]
  have e4 : (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) 1, ∫⁻ e,
      (‖LevyStochCalc.Examples.Nonvacuity.coeffs.γ s (X s ω) e 0‖₊ : ℝ≥0∞) ^ 2 ∂LevyStochCalc.Examples.Nonvacuity.jumpIntensity ∂volume ∂P) = 1 := by
    have hpt : ∀ (ω : Ω) (s : ℝ), (∫⁻ e, (‖LevyStochCalc.Examples.Nonvacuity.coeffs.γ s (X s ω) e 0‖₊ : ℝ≥0∞) ^ 2
        ∂LevyStochCalc.Examples.Nonvacuity.jumpIntensity) = 1 := by
      intro ω s
      simp only [LevyStochCalc.Examples.Nonvacuity.jumpIntensity, coeffs_gamma_apply]
      rw [lintegral_dirac]
      simp
    simp only [hpt, lintegral_const, measure_univ, mul_one, Measure.restrict_apply_univ,
      Real.volume_Icc, sub_zero, ENNReal.ofReal_one]
  have key := _root_.Prove2MeSourceProof.h_f574d7521b7b37d4f4a7a428
    (LevyStochCalc.Examples.Nonvacuity.isItoLevyProcess_of_solvesOn hXm hXsol) 𝒲 stronglyMeasurable_const (memLp_const (0 : ℝ))
    hbm hbp hbq (T := 1) one_pos
  rw [key]
  simp only [e3, e4, Fin.sum_univ_one, ENNReal.toReal_one]
  simp_rw [e2]
  norm_num
end Solution

/-! ### The filtration of the construction -/

variable (D : LevyDriver P 1 jumpIntensity)

/-! ### The witness -/

end LevyStochCalc.Examples.Nonvacuity


