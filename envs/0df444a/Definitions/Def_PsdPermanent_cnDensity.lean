-- Prove2me | Definitions.Def_PsdPermanent_cnDensity
-- name    : PsdPermanent_cnDensity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:30:46.240681+00:00
-- url     : https://prove2.me/theorems/7574235b-ca90-4799-9831-62457ceab66f
-- title:
--   The density of the complex Gaussian $\mathcal{CN}(0,X)$
-- statement:
--   For a Hermitian positive definite $d\times d$ matrix $X$, the circularly symmetric complex Gaussian $\mathcal{CN}(0,X)$ has density
--   $$z\longmapsto\frac{1}{\pi^d\det X}\exp(-z^\dagger X^{-1}z)$$
--   with respect to Lebesgue measure on $\mathbb C^d\cong\mathbb R^{2d}$.
--
--   **Formalization Note** Lebesgue measure is the product measure on `Fin d → ℂ`. Real parts of $\det X$ and $z^\dagger X^{-1}z$ are taken; both are real for positive definite $X$.
-- source:
--   N. Anari, F. Ebrahimnejad, Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive Semidefinite Matrices, arXiv:2605.21946 (held copy sha256 5e70fa63…), §3, p.3

import Mathlib
open Matrix

namespace PsdPermanent

/-- **The density of the complex Gaussian CN(0, X).**
Anari, Ebrahimnejad, *Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive
Semidefinite Matrices*, arXiv:2605.21946 (held copy sha256 5e70fa63…), §3, p.3: "Z ∼ CN(0, X), for X ∈ H_d^{++}, has density (1 / (π^d det X)) exp(−z† X^{−1} z)".

**Formalization Note.** A density with respect to `volume` on `Fin d → ℂ`, the product of Lebesgue
measure on `ℂ ≅ ℝ²` (the identification `C^d ≅ R^{2d}` with unit Jacobian). For `X` positive definite
the quantities `det X` and `z†X⁻¹z` are real, so the real parts lose nothing. -/
noncomputable def cnDensity {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) (z : Fin d → ℂ) : ℝ :=
  (Real.pi ^ d * X.det.re)⁻¹ * Real.exp (-(star z ⬝ᵥ (X⁻¹ *ᵥ z)).re)

end PsdPermanent


