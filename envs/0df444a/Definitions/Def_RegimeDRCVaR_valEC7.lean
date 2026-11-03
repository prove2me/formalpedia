-- Prove2me | Definitions.Def_RegimeDRCVaR_valEC7
-- name    : RegimeDRCVaR_valEC7
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:24:13.428213+00:00
-- url     : https://prove2.me/theorems/5abdaa41-31c6-4444-a26c-ae7b80fbc2e6
-- title:
--   Optimal value of problem (EC.7)
-- statement:
--   The optimal value of problem (EC.7) is
--   $$
--   \min_{v,x,\boldsymbol\alpha,\boldsymbol\beta}\ v+\frac{1}{1-\eta}\Big[\sum_{k\in[K]}\sum_{n\in[N_k]}\frac{w_k}{N_k}\alpha_{nk}+\sum_{k\in[K]}\beta_k w_k\theta_k\Big]
--   $$
--   over the feasible set of (EC.7).
--
--   **Formalization Note** The minimum is an infimum in the extended reals, $+\infty$ on an empty feasible set.
-- source:
--   Pun, Wang, Yan, Data-Driven Distributionally Robust CVaR Portfolio Optimization under Regime-Switching Ambiguity Set, SSRN 4378930, proof of Theorem 1, display (EC.7), p.ec3

import Mathlib
import Definitions.Def_RegimeDRCVaR_feasEC7
import Definitions.Def_RegimeDRCVaR_objEC3

open scoped ENNReal

namespace RegimeDRCVaR

/-- **The optimal value of problem (EC.7)**
`min_{v,x,α,β} v + (1 − η)⁻¹ [∑_{k∈[K]} ∑_{n∈[N_k]} (w_k/N_k) α_{nk} + ∑_{k∈[K]} β_k w_kθ_k]`
over the feasible set of (EC.7)
(Pun, Wang, Yan, *Data-Driven Distributionally Robust CVaR Portfolio Optimization under Regime-Switching Ambiguity Set*, SSRN 4378930, proof of Theorem 1, display (EC.7), p.ec3).

**Formalization Note** The bracket is the (EC.3) objective `objEC3`. The "min" is an infimum in
`EReal`, `+∞` on an empty feasible set. -/
noncomputable def valEC7 {I K p q : ℕ} {N : Fin K → ℕ} (m : ℝ≥0∞)
    (r : (k : Fin K) → Fin (N k) → Fin I → ℝ) (w θ : Fin K → ℝ) (η : ℝ)
    (A : Matrix (Fin p) (Fin I) ℝ) (b : Fin p → ℝ) (C : Matrix (Fin q) (Fin I) ℝ)
    (d : Fin q → ℝ) : EReal :=
  ⨅ (v : ℝ) (x : Fin I → ℝ) (α : (k : Fin K) → Fin (N k) → ℝ) (β : Fin K → ℝ)
    (_ : feasEC7 m r A b C d v x α β), ((v + (1 - η)⁻¹ * objEC3 w θ α β : ℝ) : EReal)

end RegimeDRCVaR


