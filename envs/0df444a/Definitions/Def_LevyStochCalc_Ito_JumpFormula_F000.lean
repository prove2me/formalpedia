-- Prove2me | Definitions.Def_LevyStochCalc_Ito_JumpFormula_F000
-- name    : LevyStochCalc_Ito_JumpFormula_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:16:11.612427+00:00
-- url     : https://prove2.me/theorems/85815950-4a8d-461c-a053-71628899ed89
-- title:
--   Source declarations: LevyStochCalc.Ito.JumpFormula
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.JumpFormula. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_Setting_F000
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô-Lévy formula for jump diffusions

For `u ∈ C^{1,2}([0,T] × ℝⁿ)` and `X` a jump diffusion driven by
`(W, N)` with coefficients `(μ, σ, γ)`,

  `u(T, X_T) − u(0, X_0)`
  `= ∫_0^T (∂_t u + 𝓛u)(s, X_{s-}) ds`
  `+ ∫_0^T ∇u(s, X_{s-})ᵀ σ(s, X_{s-}) dW_s`
  `+ ∫_0^T ∫_E [u(s, X_{s-} + γ(s, X_{s-}, e)) − u(s, X_{s-})] Ñ(ds, de)`
  `+ ∫_0^T ∫_E [u(·+γ) − u − γᵀ ∇u](s, X_{s-}, e) ν(de) ds`,

where `𝓛u = μᵀ ∇u + ½ Tr(σ σᵀ ∇²u)` is the diffusion generator.

## Source

* Applebaum 2009, Theorem 4.4.7.

## Structure

This module holds the integrand vocabulary of the formula: `gradient`, `hessian`, `timeDeriv`,
`levyGenerator`, `driftIntegrand`, `diffusionIntegrand` and `compensatorDriftIntegrand`. The
formula itself is `itoLevyFormula_of_boundedDerivs` in `Ito/ItoLevyBoundedDerivsSolution.lean`:
the four-term identity for a state function with bounded first and second derivatives, relative
to the filtration of the solution's SDE data. The general statement, with no bound on the
derivatives, is the theorem `itoLevyFormula_general` (`Ito/ItoLevyFormulaGeneral.lean`), built
on the bounded-derivative case above. The formulation
`itoLevyFormula_jumpResidual_canonical_axiom`, asserting the identity at an arbitrary
filtration unrelated to the one the solution solves against, cannot be proved as stated
(`tools/cited_axioms.md`, `Resolved #16`).
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpFormula

universe u v

section Integrands
variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- Gradient of `u : ℝ → (Fin n → ℝ) → ℝ` in its space argument, returning a
`Fin n → ℝ` vector. Equals `fderiv ℝ (u s) x (Pi.single i 1)` for each
component i; for non-differentiable u, Mathlib's `fderiv` returns 0 so
the gradient is 0. -/
noncomputable def gradient {n : ℕ} (u : ℝ → (Fin n → ℝ) → ℝ)
    (s : ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => fderiv ℝ (u s) x (Pi.single i 1)
/-- Row product `(∇u)ᵀ σ : Fin d → ℝ` of the gradient row vector with the
diffusion matrix `σ : Fin n → Fin d → ℝ`. -/
noncomputable def diffusionIntegrand {n d : ℕ}
    (u : ℝ → (Fin n → ℝ) → ℝ)
    (σ : ℝ → (Fin n → ℝ) → (Fin n → Fin d → ℝ))
    (s : ℝ) (x : Fin n → ℝ) : Fin d → ℝ :=
  fun j => ∑ i : Fin n, gradient u s x i * σ s x i j
/-- Compensator-drift integrand `u(s, x + γ(s, x, e)) − u(s, x) − γ(s, x, e)ᵀ ∇u(s, x)`.
This is the inner integrand of the compensator-drift term in the Itô–Lévy
formula (the Lévy-generator correction integrated against `ν(de) ds`). -/
noncomputable def compensatorDriftIntegrand {n : ℕ} {E : Type v}
    (u : ℝ → (Fin n → ℝ) → ℝ)
    (γ : ℝ → (Fin n → ℝ) → E → (Fin n → ℝ))
    (s : ℝ) (x : Fin n → ℝ) (e : E) : ℝ :=
  u s (x + γ s x e) - u s x - ∑ i : Fin n, γ s x e i * gradient u s x i
/-- Time derivative `∂_t u (s, x)`. Returns 0 if u is not differentiable in t
at (s, x). -/
noncomputable def timeDeriv {n : ℕ} (u : ℝ → (Fin n → ℝ) → ℝ)
    (s : ℝ) (x : Fin n → ℝ) : ℝ :=
  deriv (fun t => u t x) s
/-- Hessian `∇²u (s, x) : Fin n → Fin n → ℝ`. Returns 0 entries where u is not
twice differentiable. -/
noncomputable def hessian {n : ℕ} (u : ℝ → (Fin n → ℝ) → ℝ)
    (s : ℝ) (x : Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => fderiv ℝ (fun y => fderiv ℝ (u s) y (Pi.single i 1)) x (Pi.single j 1)
/-- The Lévy generator `Lu(s, x) := μᵀ∇u + ½Tr(σσᵀ∇²u)` (the continuous part;
the jump part is integrated into `comp_drift`'s integrand). -/
noncomputable def levyGenerator {n d : ℕ}
    (u : ℝ → (Fin n → ℝ) → ℝ)
    (μ : ℝ → (Fin n → ℝ) → (Fin n → ℝ))
    (σ : ℝ → (Fin n → ℝ) → (Fin n → Fin d → ℝ))
    (s : ℝ) (x : Fin n → ℝ) : ℝ :=
  (∑ i : Fin n, μ s x i * gradient u s x i)
  + (1 / 2) * (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin d,
      σ s x i k * σ s x j k * hessian u s x i j)
/-- Drift-term integrand `(∂_t u + Lu)(s, x)`. -/
noncomputable def driftIntegrand {n d : ℕ}
    (u : ℝ → (Fin n → ℝ) → ℝ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (s : ℝ) (x : Fin n → ℝ) : ℝ :=
  timeDeriv u s x + levyGenerator u coeffs.μ coeffs.σ s x
end Integrands

end LevyStochCalc.Ito.JumpFormula


