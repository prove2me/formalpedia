-- Prove2me | Definitions.Def_SourceProof_fbf2bdb2e46963ef0b18b08d
-- name    : SourceProof_fbf2bdb2e46963ef0b18b08d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:36:15.220506+00:00
-- url     : https://prove2.me/theorems/7550ca57-e73b-47e4-95bc-dd0fc8733cde
-- title:
--   LevyStochCalc source module: SourceProof_fbf2bdb2e46963ef0b18b08d
-- statement:
--   The original source theorem `LevyStochCalc.Examples.Nonvacuity.coeffs_isRegular` comes from the `NonvacuityItoLevy` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_NonvacuityItoLevy_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# A jump diffusion satisfying the hypotheses of the Itô–Lévy formula

The scalar jump diffusion `dX_t = dW_t + ∫_ℝ e Ñ(dt, de)` with `X_0 = 0`, driven by a
one-dimensional Brownian motion and a Poisson random measure of intensity `dt ⊗ δ_1` on
`[0, ∞) × ℝ`, together with the state function `u(t, x) = x₀²` on the horizon `[0, 1]`.

The coefficients `μ = 0`, `σ = 1`, `γ(s, x, e) = e` are regular and Lipschitz with constant
`0`, so the SDE has a solution, and `u` is `C²` with gradient `∇u(s, x) = 2x₀`, diffusion
integrand `(∇u)ᵀσ = 2x₀`, jump increment `u(x + e) − u(x) = 2ex₀ + e²` and compensator drift
`u(x + e) − u(x) − e∇u(x) = e²`. The derived energies are finite because the solution has a
finite `S²` norm on every window, and the compensator drift is the constant `1`.

The gradient of `u` is unbounded, so `u` lies outside the range of the Itô–Lévy formula for a
state function with bounded first and second derivatives.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Examples.Nonvacuity

open LevyStochCalc.Ito.Setting LevyStochCalc.Ito.JumpFormula

/-! ### The model -/

/-! ### Regularity of the coefficients -/


theorem _root_.Prove2MeSourceProof.h_fbf2bdb2e46963ef0b18b08d : coeffs.IsRegular jumpIntensity := by
  refine ⟨LevyStochCalc.Examples.Nonvacuity.measurable_uncurry_mu, LevyStochCalc.Examples.Nonvacuity.measurable_uncurry_sigma, LevyStochCalc.Examples.Nonvacuity.measurable_gamma, ?_, ?_, ?_⟩
  · intro T _
    simp [LevyStochCalc.Examples.Nonvacuity.coeffs]
  · intro T _
    simp only [LevyStochCalc.Examples.Nonvacuity.coeffs, Fin.sum_univ_one, nnnorm_one, ENNReal.coe_one, one_pow,
      setLIntegral_one, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  · intro T _
    have hinner : ∀ s : ℝ, ∫⁻ e, (‖LevyStochCalc.Examples.Nonvacuity.coeffs.γ s 0 e‖₊ : ℝ≥0∞) ^ 2 ∂LevyStochCalc.Examples.Nonvacuity.jumpIntensity
        = (‖(fun _ : Fin 1 => (1 : ℝ))‖₊ : ℝ≥0∞) ^ 2 := by
      intro s
      simp only [LevyStochCalc.Examples.Nonvacuity.jumpIntensity, LevyStochCalc.Examples.Nonvacuity.coeffs]
      exact lintegral_dirac _ _
    simp only [hinner, setLIntegral_const, Real.volume_Icc]
    exact ENNReal.mul_lt_top (by simp) ENNReal.ofReal_lt_top
/-! ### The derivatives of `u(t, x) = x₀²` -/

/-! ### Finite energy along an `S²`-bounded path -/

section Energy

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

end Energy

/-! ### The witness -/

open LevyStochCalc.Brownian.Multidim (MultidimBrownianMotion)
open LevyStochCalc.Poisson (PoissonRandomMeasure)
open LevyStochCalc.Ito.BigJump (SdeData)

end LevyStochCalc.Examples.Nonvacuity

-- P2M_SOURCE_AUDIT_ONLY: #print axioms LevyStochCalc.Examples.Nonvacuity.itoLevyFormula_general_nonvacuous


