-- Prove2me | Definitions.Def_PsdPermanent_realGaussianDensity
-- name    : PsdPermanent_realGaussianDensity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:30:49.300314+00:00
-- url     : https://prove2.me/theorems/c1e26fe9-1f0d-4237-85d3-4d48d14025ed
-- title:
--   The density of the real Gaussian $N(m,S)$
-- statement:
--   For $m\in\mathbb R^k$ and a positive definite $S$, the real Gaussian $N(m,S)$ has density
--   $$y\longmapsto\big((2\pi)^k\det S\big)^{-1/2}\exp\Big(-\tfrac12(y-m)^\top S^{-1}(y-m)\Big)$$
--   with respect to Lebesgue measure on $\mathbb R^k$.
-- source:
--   N. Anari, F. Ebrahimnejad, Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive Semidefinite Matrices, arXiv:2605.21946 (held copy sha256 5e70fa63…), Lemma 2, p.4

import Mathlib
open Matrix

namespace PsdPermanent

/-- **The density of the real Gaussian N(m, S).**
Anari, Ebrahimnejad, *Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive
Semidefinite Matrices*, arXiv:2605.21946 (held copy sha256 5e70fa63…), Lemma 2, p.4: "N(E[Y], Σ)".

`realGaussianDensity m S y = ((2π)^k det S)^{−1/2} exp(−½ (y − m)ᵀ S⁻¹ (y − m))`, the standard density
with respect to Lebesgue measure on `R^k`.

**Formalization Note.** It is a density when `S` is positive definite, which is automatic for the
covariance of a density when it is nonsingular. -/
noncomputable def realGaussianDensity {k : ℕ} (m : Fin k → ℝ) (S : Matrix (Fin k) (Fin k) ℝ)
    (y : Fin k → ℝ) : ℝ :=
  (Real.sqrt ((2 * Real.pi) ^ k * S.det))⁻¹ * Real.exp (-(1 / 2 * ((y - m) ⬝ᵥ (S⁻¹ *ᵥ (y - m)))))

end PsdPermanent


