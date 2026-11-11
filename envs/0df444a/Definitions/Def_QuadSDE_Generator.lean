-- Prove2me | Definitions.Def_QuadSDE_Generator
-- name    : QuadSDE_Generator
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:15:30.498447+00:00
-- url     : https://prove2.me/theorems/934930f9-0315-4ad7-8456-e01e7fcf4f7a
-- title:
--   The drift derivative $f\cdot\nabla$ and the generator $G_t$ on polynomials
-- statement:
--   For a drift with coefficients $c_{ijk}$ write $f_i=\sum_{j,k}c_{ijk}x_jx_k$ as a polynomial. On a real polynomial $\varphi$ in $x_1,\dots,x_N$ define
--   $$(f\cdot\nabla)\varphi=\sum_if_i\,\partial_i\varphi,\qquad G_t\varphi=\lambda(t)\big(\Delta\varphi-x\cdot\nabla\varphi\big)+\sqrt{\rho(t)}\,(f\cdot\nabla)\varphi \qquad(31),$$
--   with $\rho(t)=p+qt$ and $\lambda(t)=q/(2\rho(t))$. $G_t$ is the generator of the rescaled process $\tilde X(t)=X(t)/\sqrt{\rho(t)}$, and $G_t\varphi$ is again a polynomial.
--
--   **Formalization Note** Polynomials are `MvPolynomial (Fin N) ℝ`, with partial derivatives `pderiv`.
-- source:
--   Bravyi, Byrne, Zayats, Zhuk, Zlokapa, Quantum algorithms for stochastic nonlinear differential equations, arXiv:2606.08349 (sha256 29bd9b01…94cdf), §4.1, Lemma 4, Eq. (31), p. 18; §4.2, p. 19

import Mathlib
import Definitions.Def_QuadSDE_DriftClass
import Definitions.Def_QuadSDE_Frame

open MvPolynomial

noncomputable section

namespace QuadSDE

/-- Bravyi–Byrne–Zayats–Zhuk–Zlokapa, arXiv:2606.08349 (sha256 29bd9b01…), Eq. (5), p. 3: the
component `f_i = Σ_{j,k} c_{ijk} x_j x_k` of the drift as a polynomial in `x_1, …, x_N`. -/
def driftPoly {N : ℕ} (c : Coeff N) (i : Fin N) : MvPolynomial (Fin N) ℝ :=
  ∑ j, ∑ k, C (c i j k) * X j * X k

/-- §4.2, p. 19: the drift derivative `(f · ∇) φ = Σ_i f_i ∂_i φ` of a polynomial `φ`. -/
def driftDeriv {N : ℕ} (c : Coeff N) (φ : MvPolynomial (Fin N) ℝ) : MvPolynomial (Fin N) ℝ :=
  ∑ i, driftPoly c i * pderiv i φ

/-- Lemma 4, Eq. (31), p. 18: the generator of the rescaled process acting on a polynomial `φ`,
`G_t φ = λ(t)(Δφ − x · ∇φ) + √ρ(t) (f · ∇) φ`, with `ρ(t) = p + qt` and `λ(t) = q/(2ρ(t))`. -/
def genPoly {N : ℕ} (c : Coeff N) (p q t : ℝ) (φ : MvPolynomial (Fin N) ℝ) :
    MvPolynomial (Fin N) ℝ :=
  C (lam p q t) * (∑ i, pderiv i (pderiv i φ) - ∑ i, X i * pderiv i φ) +
    C (Real.sqrt (rho p q t)) * driftDeriv c φ

end QuadSDE


