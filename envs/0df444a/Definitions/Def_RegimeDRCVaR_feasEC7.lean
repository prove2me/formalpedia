-- Prove2me | Definitions.Def_RegimeDRCVaR_feasEC7
-- name    : RegimeDRCVaR_feasEC7
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:23:22.759202+00:00
-- url     : https://prove2.me/theorems/b0a07911-d8c8-48d0-ab08-3cbccad4d417
-- title:
--   Feasible set of problem (EC.7)
-- statement:
--   A point $(v,x,\boldsymbol\alpha,\boldsymbol\beta)$ with one multiplier $\beta_k$ per regime is **feasible for (EC.7)** if
--
--   1. $r_{nk}'x\ge-\alpha_{nk}-v$ for all $n\in[N_k]$, $k\in[K]$;
--   2. $\beta_k\ge\|x\|_{m^*}$ for all $k\in[K]$;
--   3. $\alpha_{nk}\ge0$ for all $n\in[N_k]$, $k\in[K]$;
--   4. $x\in\mathcal X$.
--
--   (EC.7) is the finite reformulation of (11) before the multipliers $\beta_k$ are merged into a single $\beta$, which gives (12).
-- source:
--   Pun, Wang, Yan, Data-Driven Distributionally Robust CVaR Portfolio Optimization under Regime-Switching Ambiguity Set, SSRN 4378930, proof of Theorem 1, display (EC.7), p.ec3

import Mathlib
import Definitions.Def_RegimeDRCVaR_normM
import Definitions.Def_RegimeDRCVaR_feasX

open Matrix
open scoped ENNReal

namespace RegimeDRCVaR

/-- **The feasible set of problem (EC.7)**
(Pun, Wang, Yan, *Data-Driven Distributionally Robust CVaR Portfolio Optimization under Regime-Switching Ambiguity Set*, SSRN 4378930, proof of Theorem 1, display (EC.7), p.ec3):
`(v, x, α, β)`, with one multiplier `β_k` per regime, is feasible iff
1. `r′_{nk} x ≥ −α_{nk} − v` for all `n ∈ [N_k]`, `k ∈ [K]`;
2. `β_k ≥ ‖x‖_{m*}` for all `k ∈ [K]`;
3. `α_{nk} ≥ 0` for all `n ∈ [N_k]`, `k ∈ [K]`;
4. `x ∈ 𝒳`.

**Formalization Note** `‖x‖_{m*}` is `normM (ENNReal.conjExponent m) x`. -/
def feasEC7 {I K p q : ℕ} {N : Fin K → ℕ} (m : ℝ≥0∞)
    (r : (k : Fin K) → Fin (N k) → Fin I → ℝ)
    (A : Matrix (Fin p) (Fin I) ℝ) (b : Fin p → ℝ) (C : Matrix (Fin q) (Fin I) ℝ)
    (d : Fin q → ℝ) (v : ℝ) (x : Fin I → ℝ) (α : (k : Fin K) → Fin (N k) → ℝ)
    (β : Fin K → ℝ) : Prop :=
  (∀ k n, -(α k n) - v ≤ r k n ⬝ᵥ x) ∧
  (∀ k, normM (ENNReal.conjExponent m) x ≤ β k) ∧
  (∀ k n, 0 ≤ α k n) ∧
  x ∈ feasX A b C d

end RegimeDRCVaR


