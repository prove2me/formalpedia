-- Prove2me | Definitions.Def_HunterPDE_Newtonian_NewtonianPotential
-- name    : HunterPDE_Newtonian_NewtonianPotential
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T23:12:26.001381+00:00
-- url     : https://prove2.me/theorems/a2cd3ca0-9f5e-405c-9f01-73f802359f7c
-- title:
--   Eq. (2.24) — the Newtonian potential u = Γ ∗ f
-- statement:
--   For a source density $f : \mathbb{R}^n \to \mathbb{R}$, the **Newtonian potential** of $f$ is the convolution of $f$ with the fundamental solution $\Gamma$,
--   $$u(x) = (\Gamma * f)(x) = \int_{\mathbb{R}^n} \Gamma(x - y)\, f(y)\, dy.$$
--   It superposes the point-source potentials $\Gamma(x - y)$ with strengths $f(y)\,dy$, and for smooth compactly supported $f$ it solves Poisson's equation $-\Delta u = f$.
--
--   **Formalization Note.** The integral is the Lebesgue (Bochner) integral over `EuclideanSpace ℝ (Fin n)` with respect to `volume`. $\Gamma$ is only locally integrable, so no integrability of $\Gamma$ is assumed; for $f \in C_c^\infty(\mathbb{R}^n)$ the integrand is integrable, which Theorem 2.25 in this mission asserts explicitly.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 36, Eq. (2.24)

import Mathlib
import Definitions.Def_HunterPDE_Newtonian_FundamentalSolution

namespace HunterPDE.Newtonian

open MeasureTheory

/-- The Newtonian potential `u = Γ ∗ f` of a source `f : ℝⁿ → ℝ`, (2.24) of Hunter, *Notes on
PDEs* (p. 36): `u(x) = ∫ Γ(x − y) f(y) dy`, a Lebesgue (Bochner) integral over `ℝⁿ` with
respect to `volume`. For `f ∈ C_c^∞(ℝⁿ)` the integrand is integrable because `Γ` is locally
integrable; no integrability of `Γ` itself is assumed. -/
noncomputable def newtonianPotential (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∫ y, fundamentalSolution n (x - y) * f y

end HunterPDE.Newtonian


