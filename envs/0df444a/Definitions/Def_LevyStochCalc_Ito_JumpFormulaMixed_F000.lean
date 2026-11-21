-- Prove2me | Definitions.Def_LevyStochCalc_Ito_JumpFormulaMixed_F000
-- name    : LevyStochCalc_Ito_JumpFormulaMixed_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:19:48.445109+00:00
-- url     : https://prove2.me/theorems/085f6bb1-0ac5-42a6-b6bb-77be445e89a1
-- title:
--   Source declarations: LevyStochCalc.Ito.JumpFormulaMixed
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.JumpFormulaMixed. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpFormula_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Mixed integrands of the Itô–Lévy formula

The integrands of the Itô–Lévy formula read the derivatives of the state function `u` and the
coefficients `(μ, σ, γ)` at a common state. The mixed integrands below separate the two: the
derivatives of `u` are taken at a state `y` and the coefficients at a state `x`. They are the
integrands that appear when the formula is written along one process while its coefficients are
read along another, e.g. an approximating process and its limit; at `y = x` they are the
integrands of `LevyStochCalc.Ito.JumpFormula`.

## Main definitions

* `LevyStochCalc.Ito.JumpFormula.mixedDriftIntegrand` —
  `∂_t u(s, y) + μ(s, x)ᵀ ∇u(s, y) + ½ Tr(σσᵀ(s, x) ∇²u(s, y))`.
* `LevyStochCalc.Ito.JumpFormula.mixedDiffusionIntegrand` — the row product `∇u(s, y)ᵀ σ(s, x)`.
* `LevyStochCalc.Ito.JumpFormula.mixedJumpIncrement` — `u(s, y + γ(s, x, e)) − u(s, y)`.
* `LevyStochCalc.Ito.JumpFormula.mixedCompensatorDriftIntegrand` —
  `u(s, y + γ(s, x, e)) − u(s, y) − γ(s, x, e)ᵀ ∇u(s, y)`.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.mixedDriftIntegrand_self`,
  `LevyStochCalc.Ito.JumpFormula.mixedDiffusionIntegrand_self`,
  `LevyStochCalc.Ito.JumpFormula.mixedJumpIncrement_self`,
  `LevyStochCalc.Ito.JumpFormula.mixedCompensatorDriftIntegrand_self` — at a common state the
  mixed integrands are the integrands of the Itô–Lévy formula.
-/

open LevyStochCalc.Ito.Setting

namespace LevyStochCalc.Ito.JumpFormula

universe v

section Mixed

variable {E : Type v} {n d : ℕ}

/-- Drift integrand `∂_t u(s, y) + μ(s, x)ᵀ ∇u(s, y) + ½ Tr(σσᵀ(s, x) ∇²u(s, y))` with the
derivatives of `u` at `y` and the coefficients at `x`. -/
noncomputable def mixedDriftIntegrand (u : ℝ → (Fin n → ℝ) → ℝ)
    (coeffs : JumpDiffusionCoeffs n d E) (s : ℝ) (y x : Fin n → ℝ) : ℝ :=
  timeDeriv u s y
    + ((∑ i : Fin n, coeffs.μ s x i * gradient u s y i)
      + (1 / 2) * (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin d,
          coeffs.σ s x i k * coeffs.σ s x j k * hessian u s y i j))
/-- Row product `∇u(s, y)ᵀ σ(s, x) : Fin d → ℝ` with the gradient at `y` and the diffusion
matrix at `x`. -/
noncomputable def mixedDiffusionIntegrand (u : ℝ → (Fin n → ℝ) → ℝ)
    (σ : ℝ → (Fin n → ℝ) → (Fin n → Fin d → ℝ)) (s : ℝ) (y x : Fin n → ℝ) : Fin d → ℝ :=
  fun j => ∑ i : Fin n, gradient u s y i * σ s x i j
/-- Jump increment `u(s, y + γ(s, x, e)) − u(s, y)` of the state function at `y` displaced by
the jump size at `x`. -/
noncomputable def mixedJumpIncrement (u : ℝ → (Fin n → ℝ) → ℝ)
    (γ : ℝ → (Fin n → ℝ) → E → (Fin n → ℝ)) (s : ℝ) (y x : Fin n → ℝ) (e : E) : ℝ :=
  u s (y + γ s x e) - u s y
/-- Compensator-drift integrand `u(s, y + γ(s, x, e)) − u(s, y) − γ(s, x, e)ᵀ ∇u(s, y)` with
the state function and its gradient at `y` and the jump size at `x`. -/
noncomputable def mixedCompensatorDriftIntegrand (u : ℝ → (Fin n → ℝ) → ℝ)
    (γ : ℝ → (Fin n → ℝ) → E → (Fin n → ℝ)) (s : ℝ) (y x : Fin n → ℝ) (e : E) : ℝ :=
  u s (y + γ s x e) - u s y - ∑ i : Fin n, γ s x e i * gradient u s y i
/-- At a common state the mixed drift integrand is the drift integrand `∂_t u + 𝓛u`. -/
@[simp] theorem mixedDriftIntegrand_self (u : ℝ → (Fin n → ℝ) → ℝ)
    (coeffs : JumpDiffusionCoeffs n d E) (s : ℝ) (x : Fin n → ℝ) :
    mixedDriftIntegrand u coeffs s x x = driftIntegrand u coeffs s x := rfl
/-- At a common state the mixed diffusion integrand is the row product `(∇u)ᵀ σ`. -/
@[simp] theorem mixedDiffusionIntegrand_self (u : ℝ → (Fin n → ℝ) → ℝ)
    (σ : ℝ → (Fin n → ℝ) → (Fin n → Fin d → ℝ)) (s : ℝ) (x : Fin n → ℝ) :
    mixedDiffusionIntegrand u σ s x x = diffusionIntegrand u σ s x := rfl
/-- At a common state the mixed jump increment is the jump increment `u(x + γ) − u(x)`. -/
@[simp] theorem mixedJumpIncrement_self (u : ℝ → (Fin n → ℝ) → ℝ)
    (γ : ℝ → (Fin n → ℝ) → E → (Fin n → ℝ)) (s : ℝ) (x : Fin n → ℝ) (e : E) :
    mixedJumpIncrement u γ s x x e = u s (x + γ s x e) - u s x := rfl
/-- At a common state the mixed compensator-drift integrand is the compensator-drift
integrand `u(x + γ) − u(x) − γᵀ ∇u(x)`. -/
@[simp] theorem mixedCompensatorDriftIntegrand_self (u : ℝ → (Fin n → ℝ) → ℝ)
    (γ : ℝ → (Fin n → ℝ) → E → (Fin n → ℝ)) (s : ℝ) (x : Fin n → ℝ) (e : E) :
    mixedCompensatorDriftIntegrand u γ s x x e = compensatorDriftIntegrand u γ s x e := rfl
end Mixed

end LevyStochCalc.Ito.JumpFormula


