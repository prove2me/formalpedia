-- Prove2me | Definitions.Def_NonvacuityItoLevy_F000
-- name    : NonvacuityItoLevy_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:32:24.090822+00:00
-- url     : https://prove2.me/theorems/f528eb17-c8be-4660-8a6a-e7d7f46cb5f9
-- title:
--   Source declarations: NonvacuityItoLevy
-- statement:
--   Source-preserving extracted declarations from NonvacuityItoLevy. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_Multidim_F000
import Definitions.Def_LevyStochCalc_Ito_BigJumpDiffusion_F001
import Definitions.Def_LevyStochCalc_Ito_JumpFormula_F000
import Definitions.Def_LevyStochCalc_Ito_Setting_F000
import Definitions.Def_LevyStochCalc_Poisson_RandomMeasure_F000

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

/-- The jump intensity: the unit mass at the mark `1`, a finite nonzero measure on `ℝ`. -/
noncomputable def jumpIntensity : Measure ℝ := Measure.dirac 1
instance : IsProbabilityMeasure jumpIntensity := by
  unfold jumpIntensity
  infer_instance
/-- The intensity carries unit mass, so the Poisson part of the driver is not degenerate. -/
theorem jumpIntensity_univ : jumpIntensity Set.univ = 1 := measure_univ
/-- The coefficients of the scalar jump diffusion `dX_t = dW_t + ∫_ℝ e Ñ(dt, de)`: zero drift,
unit diffusion matrix, and a jump of size equal to the mark. -/
noncomputable def coeffs : JumpDiffusionCoeffs 1 1 ℝ where
  μ := fun _ _ => 0
  σ := fun _ _ _ _ => 1
  γ := fun _ _ e => fun _ => e
/-- The diffusion matrix is the identity, so the Brownian part of the driver is not
degenerate. -/
theorem coeffs_sigma_apply (s : ℝ) (x : Fin 1 → ℝ) (i j : Fin 1) : coeffs.σ s x i j = 1 := rfl
/-- A jump of the mark's size. -/
theorem coeffs_gamma_apply (s : ℝ) (x : Fin 1 → ℝ) (e : ℝ) (i : Fin 1) :
    coeffs.γ s x e i = e := rfl
/-- The state function `u(t, x) = x₀²`, independent of time. -/
noncomputable def uSq : ℝ → (Fin 1 → ℝ) → ℝ := fun _ x => (x 0) ^ 2
/-! ### Regularity of the coefficients -/

theorem measurable_uncurry_mu : Measurable (Function.uncurry coeffs.μ) :=
  measurable_const
theorem measurable_uncurry_sigma : Measurable (Function.uncurry coeffs.σ) :=
  measurable_const
theorem measurable_gamma :
    Measurable fun q : ℝ × (Fin 1 → ℝ) × ℝ => coeffs.γ q.1 q.2.1 q.2.2 := by
  simp only [coeffs]
  exact measurable_pi_lambda _ fun _ => measurable_snd.snd
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


