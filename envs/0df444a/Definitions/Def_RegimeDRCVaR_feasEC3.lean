-- Prove2me | Definitions.Def_RegimeDRCVaR_feasEC3
-- name    : RegimeDRCVaR_feasEC3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:23:22.324491+00:00
-- url     : https://prove2.me/theorems/187126e4-81e1-4ab1-9d53-1c88eb1593f3
-- title:
--   Feasible set of the semi-infinite dual (EC.3)
-- statement:
--   Fix a portfolio $x$ and $v\in\mathbb R$. Multipliers $\alpha_{nk}\in\mathbb R$ and $\boldsymbol\beta=(\beta_1,\dots,\beta_K)$ are **feasible for (EC.3)** if
--
--   1. $\alpha_{nk}+\beta_k u\ge -x'r-v$ for all $k\in[K]$, $n\in[N_k]$, $r\in\mathbb R^I$ and $u\in\mathbb R$ with $\rho(r,r_{nk})\le u$;
--   2. $\alpha_{nk}+\beta_k u\ge 0$ for the same $k,n,r,u$;
--   3. $\beta_k\ge 0$ for all $k$.
--
--   These are the constraints of the dual of the worst-case expectation over $\mathcal U_{rs}(\boldsymbol\theta)$; there are infinitely many of them.
--
--   **Formalization Note** $\rho(r,r_{nk})=\|r-r_{nk}\|_m$.
-- source:
--   Pun, Wang, Yan, Data-Driven Distributionally Robust CVaR Portfolio Optimization under Regime-Switching Ambiguity Set, SSRN 4378930, proof of Theorem 1, display (EC.3), p.ec2

import Mathlib
import Definitions.Def_RegimeDRCVaR_normM

open Matrix
open scoped ENNReal

namespace RegimeDRCVaR

/-- **The feasible set of the dual problem (EC.3)** at a fixed portfolio `x` and level `v`
(Pun, Wang, Yan, *Data-Driven Distributionally Robust CVaR Portfolio Optimization under Regime-Switching Ambiguity Set*, SSRN 4378930, proof of Theorem 1, display (EC.3), p.ec2):
`(α, β)` is feasible iff
1. `α_{nk} + β_k u ≥ −x′r − v` for all `k ∈ [K]`, `n ∈ [N_k]`, `r ∈ ℝ^I` and `u` with
   `ρ(r, r_{nk}) ≤ u`;
2. `α_{nk} + β_k u ≥ 0` for the same `k, n, r, u`;
3. `β_k ≥ 0` for all `k ∈ [K]`.

**Formalization Note** `ρ(r, r_{nk}) = ‖r − r_{nk}‖_m` is `normM m (r' - r k n)`; the generic return
of the constraint is `r'` (the samples are `r k n`); `u` ranges over `ℝ`. -/
def feasEC3 {I K : ℕ} {N : Fin K → ℕ} (m : ℝ≥0∞) (r : (k : Fin K) → Fin (N k) → Fin I → ℝ)
    (x : Fin I → ℝ) (v : ℝ) (α : (k : Fin K) → Fin (N k) → ℝ) (β : Fin K → ℝ) : Prop :=
  (∀ (k : Fin K) (n : Fin (N k)) (r' : Fin I → ℝ) (u : ℝ), normM m (r' - r k n) ≤ u →
      -(x ⬝ᵥ r') - v ≤ α k n + β k * u ∧ 0 ≤ α k n + β k * u) ∧
  ∀ k, 0 ≤ β k

end RegimeDRCVaR


