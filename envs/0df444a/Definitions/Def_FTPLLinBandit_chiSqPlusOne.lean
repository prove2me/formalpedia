-- Prove2me | Definitions.Def_FTPLLinBandit_chiSqPlusOne
-- name    : FTPLLinBandit_chiSqPlusOne
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:00:56.962075+00:00
-- url     : https://prove2.me/theorems/ef1dbc4b-dafa-4f0c-88de-75909c21cd8f
-- title:
--   $1+\chi^2(\rho(\cdot-v)\,\|\,\rho)$
-- statement:
--   For a probability density $\rho$ on $\mathbb R^d$ and $v\in\mathbb R^d$, let $\rho(\cdot-v)$ be the density of $Z+v$, $Z\sim\rho$. Then
--   $$1+\chi^2\big(\rho(\cdot-v)\,\|\,\rho\big)=\int_{\mathbb R^d}\frac{\rho(z-v)^2}{\rho(z)}\,dz\in[0,\infty].$$
--   It is the second argument of the maximum in Lemma 5; Table 2 bounds it by a universal constant for the three initializers when $\|v\|_2\le\sqrt\lambda/8$.
-- source:
--   Wei, Follow the Perturbed Leader for Linear Bandits: √T Regret over General Action Sets, arXiv:2610.17818, Lemma 5, Eq. (13), p.11; Eq. (28), p.29

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace FTPLLinBandit

/-- **`1 + χ²(ρ(· − v) ‖ ρ)`.** Wei, arXiv:2610.17818, Lemma 5, Eq. (13), p.11 ("ρ₁(· − v) is the
density of Z + v for Z ∼ ρ₁"); proof of Lemma 5, Eq. (28), p.29 (`∫ ρ_t(z − v)²/ρ_t(z) dz`).

`chiSqPlusOne ρ v = ∫ ρ(z − v)² / ρ(z) dz ∈ [0, ∞]`, which is `1 + χ²(ρ(· − v) ‖ ρ)` for a
probability density `ρ`.

**Formalization Note.** Extended nonnegative value (`∞` allowed). Where `ρ(z) = 0` Lean's quotient
is `0`; the theorems using it concern densities positive everywhere or almost everywhere. -/
noncomputable def chiSqPlusOne {d : ℕ} (ρ : EuclideanSpace ℝ (Fin d) → ℝ)
    (v : EuclideanSpace ℝ (Fin d)) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (ρ (z - v) ^ 2 / ρ z)

end FTPLLinBandit


