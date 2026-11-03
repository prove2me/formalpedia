-- Prove2me | Definitions.Def_RegimeDRCVaR_dualCone
-- name    : RegimeDRCVaR_dualCone
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:22:43.364544+00:00
-- url     : https://prove2.me/theorems/17d97308-dc02-4a25-9935-f6b75b7e230e
-- title:
--   Dual cone $\bar K^*$ in $\mathbb R^{I+1}$
-- statement:
--   For a set $\bar K\subseteq\mathbb R^{I+1}$, the **dual cone** is
--   $$
--   \bar K^*=\{y \mid y'z\ge 0\ \ \forall z\in\bar K\}.
--   $$
--   It is the feasible region of the dual (EC.5) in Lemma EC.2.
--
--   **Formalization Note** $\mathbb R^{I+1}$ is $\mathbb R^I\times\mathbb R$, with the pairs $(p;u)$ of the paper and the inner product $y'z=y_1'z_1+y_2z_2$. The paper names the bound vector $x$; it is unrelated to the portfolio.
-- source:
--   Pun, Wang, Yan, Data-Driven Distributionally Robust CVaR Portfolio Optimization under Regime-Switching Ambiguity Set, SSRN 4378930, Lemma EC.2, p.ec3

import Mathlib

open Matrix

namespace RegimeDRCVaR

/-- **The dual cone** `K̄* = {y | y′z ≥ 0, ∀ z ∈ K̄}` of a set `K̄ ⊆ ℝ^{I+1}`
(Pun, Wang, Yan, *Data-Driven Distributionally Robust CVaR Portfolio Optimization under Regime-Switching Ambiguity Set*, SSRN 4378930, Lemma EC.2, p.ec3).

**Formalization Note** `ℝ^{I+1}` is `(Fin I → ℝ) × ℝ`, the pair `(p; u)` of the paper, with the
standard inner product `y′z = y.1 ⬝ z.1 + y.2 · z.2`. The paper names the bound vector "x"; it is
`z` here and has nothing to do with the portfolio. -/
def dualCone {I : ℕ} (K : Set ((Fin I → ℝ) × ℝ)) : Set ((Fin I → ℝ) × ℝ) :=
  {y | ∀ z ∈ K, 0 ≤ y.1 ⬝ᵥ z.1 + y.2 * z.2}

end RegimeDRCVaR


