-- Prove2me | Definitions.Def_SmoothNestedSim_nestedExpectation
-- name    : SmoothNestedSim_nestedExpectation
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:37:19.340263+00:00
-- url     : https://prove2.me/theorems/0f771616-eb72-4bad-a495-dc195fdde5bf
-- title:
--   Nested expectation $\theta=\mathbb E[\eta(f(X))]$
-- statement:
--   Let $X$ have law $\mu_X$, $f(\mathbf x)=\mathbb E[Y\mid X=\mathbf x]$ and $\eta:\mathbb R\to\mathbb R$. The **nested expectation** is
--
--   $$
--   \theta = \mathbb E\bigl[\eta(\mathbb E[Y\mid X])\bigr] = \int \eta(f(\mathbf x))\,\mu_X(d\mathbf x),
--   $$
--
--   the quantity $\mathcal T(\mathbb E[Y\mid X])$ of (1) for $\mathcal T(Z)=\mathbb E[\eta(Z)]$.
--
--   **Formalization Note** The expectation is a Bochner integral. Under the mission's hypotheses ($f$ in the Matérn RKHS, hence bounded and continuous on $\Omega$, and $\eta$ continuous) the integrand is bounded and measurable.
-- source:
--   Wang, Wang, Zhang, Smooth Nested Simulation: Bridging Cubic and Square Root Convergence Rates in High Dimensions, arXiv:2201.02958v6, (1), p.1; §2 (i), p.8; §4.2, p.16

import Mathlib

open MeasureTheory

namespace SmoothNestedSim

/-- **The nested expectation `θ = 𝔼[η(f(X))]`** (Wang, Wang, Zhang, *Smooth Nested
Simulation*, arXiv:2201.02958v6, (1), p.1 with `𝒯(Z) = 𝔼[η(Z)]` from §2 (i), p.8, and §4.2,
p.16: `θ = 𝔼[η(𝔼[Y|X])]`, `f(x) = 𝔼[Y | X = x]`), where `X` has law `μX`.

**Formalization Note.** The expectation is the Bochner integral of `η ∘ f` against `μX`. Under
the mission's hypotheses (`f` in the Matérn RKHS, hence continuous and bounded on `Ω`, and `η`
continuous) the integrand is bounded and measurable, so the integral is not Lean's junk value. -/
noncomputable def nestedExpectation {d : ℕ} (μX : Measure (EuclideanSpace ℝ (Fin d)))
    (η : ℝ → ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ) : ℝ :=
  ∫ x, η (f x) ∂μX

end SmoothNestedSim


