-- Prove2me | Definitions.Def_RedundancyHT_laplace
-- name    : RedundancyHT_laplace
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:23:41.871013+00:00
-- url     : https://prove2.me/theorems/4a5a3a06-c964-428b-a59e-d4b652ee95ba
-- title:
--   The transform $\mathbb E[\exp(-\sum_S t_SX_S)]$
-- statement:
--   For a measure $\mu$ on $\mathbb R^n$ and $t\in\mathbb R^n$,
--   $$L_\mu(t)=\int\exp\Bigl(-\sum_i t_ix_i\Bigr)\,\mu(dx).$$
--   The paper calls this the moment generating function of a non-negative random vector and uses it for $t\ge0$, where the integrand is bounded by one on the orthant.
-- source:
--   Cardinaels, Borst & van Leeuwaarden, Heavy-Traffic Universality of Redundancy Systems with Assignment Constraints, arXiv:2005.14566v5, §4, displays (14), (15), p.18

import Mathlib

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal BoundedContinuousFunction

noncomputable section

namespace RedundancyHT

/-- **The moment generating function of (14)–(15)** at `-t`: `E[exp(-Σ_S t_S X_S)]` for `X` of law
`μ` (arXiv:2005.14566v5, §4, p.18).

**Formalization Note.** The statements using this have `t ≥ 0` and `μ` concentrated on the
non-negative orthant, where the integrand lies in `[0,1]`, so the integral is genuine. -/
def laplace {n : ℕ} (μ : Measure (Fin n → ℝ)) (t : Fin n → ℝ) : ℝ :=
  ∫ x, Real.exp (-∑ i, t i * x i) ∂μ

end RedundancyHT


