-- Prove2me | Definitions.Def_RegimeDRCVaR_feas12
-- name    : RegimeDRCVaR_feas12
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:23:34.243597+00:00
-- url     : https://prove2.me/theorems/bd2c7042-e7fa-4809-9742-43e925326955
-- title:
--   Feasible set of problem (12)
-- statement:
--   A point $(v,x,\boldsymbol\alpha,\beta)$, with $v,\beta\in\mathbb R$, $x\in\mathbb R^I$ and $\alpha_{nk}\in\mathbb R$, is **feasible for (12)** if
--
--   1. $r_{nk}'x\ge-\alpha_{nk}-v$ for all $n\in[N_k]$, $k\in[K]$;
--   2. $\beta\ge\|x\|_{m^*}$;
--   3. $\alpha_{nk}\ge 0$ for all $n\in[N_k]$, $k\in[K]$;
--   4. $x\in\mathcal X$.
--
--   Constraint 2 is the only nonlinear one: for $m=1$ it is a set of linear inequalities, for $m=2$ a second-order cone constraint.
--
--   **Formalization Note** $\|x\|_{m^*}$ is the $\ell_{m^*}$ norm with the conjugate exponent `ENNReal.conjExponent m`.
-- source:
--   Pun, Wang, Yan, Data-Driven Distributionally Robust CVaR Portfolio Optimization under Regime-Switching Ambiguity Set, SSRN 4378930, Theorem 1, display (12), p.13

import Mathlib
import Definitions.Def_RegimeDRCVaR_normM
import Definitions.Def_RegimeDRCVaR_feasX

open Matrix
open scoped ENNReal

namespace RegimeDRCVaR

/-- **The feasible set of problem (12)**
(Pun, Wang, Yan, *Data-Driven Distributionally Robust CVaR Portfolio Optimization under Regime-Switching Ambiguity Set*, SSRN 4378930, Theorem 1, display (12), p.13): `(v, x, α, β)` is feasible iff
1. `r′_{nk} x ≥ −α_{nk} − v` for all `n ∈ [N_k]`, `k ∈ [K]`;
2. `β ≥ ‖x‖_{m*}`;
3. `α_{nk} ≥ 0` for all `n ∈ [N_k]`, `k ∈ [K]`;
4. `x ∈ 𝒳`.

**Formalization Note** `‖x‖_{m*}` is `normM (ENNReal.conjExponent m) x`, the ℓ_{m*} norm with
`1/m + 1/m* = 1` ("m* is the conjugate norm", p.ec4). `α` is indexed as `α k n`. -/
def feas12 {I K p q : ℕ} {N : Fin K → ℕ} (m : ℝ≥0∞)
    (r : (k : Fin K) → Fin (N k) → Fin I → ℝ)
    (A : Matrix (Fin p) (Fin I) ℝ) (b : Fin p → ℝ) (C : Matrix (Fin q) (Fin I) ℝ)
    (d : Fin q → ℝ) (v : ℝ) (x : Fin I → ℝ) (α : (k : Fin K) → Fin (N k) → ℝ) (β : ℝ) : Prop :=
  (∀ k n, -(α k n) - v ≤ r k n ⬝ᵥ x) ∧
  normM (ENNReal.conjExponent m) x ≤ β ∧
  (∀ k n, 0 ≤ α k n) ∧
  x ∈ feasX A b C d

end RegimeDRCVaR


