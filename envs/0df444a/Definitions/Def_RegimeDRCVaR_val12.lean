-- Prove2me | Definitions.Def_RegimeDRCVaR_val12
-- name    : RegimeDRCVaR_val12
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:24:50.463494+00:00
-- url     : https://prove2.me/theorems/8f61c307-e6e3-4b94-b00d-c8621162ea65
-- title:
--   Optimal value of problem (12)
-- statement:
--   The optimal value of problem (12) is
--   $$
--   \min_{v,x,\boldsymbol\alpha,\beta}\ v+\frac{1}{1-\eta}\Big[\sum_{k\in[K]}\sum_{n\in[N_k]}\frac{w_k}{N_k}\alpha_{nk}+\beta\sum_{k\in[K]}w_k\theta_k\Big]
--   $$
--   over the feasible set of (12).
--
--   **Formalization Note** The minimum is an infimum in the extended reals; it is $+\infty$ when the feasible set is empty, which happens exactly when $\mathcal X$ is empty.
-- source:
--   Pun, Wang, Yan, Data-Driven Distributionally Robust CVaR Portfolio Optimization under Regime-Switching Ambiguity Set, SSRN 4378930, Theorem 1, display (12), p.13

import Mathlib
import Definitions.Def_RegimeDRCVaR_feas12
import Definitions.Def_RegimeDRCVaR_obj12

open scoped ENNReal

namespace RegimeDRCVaR

/-- **The optimal value of problem (12)**
`min_{v, x, α, β}` of the objective of (12) over its feasible set
(Pun, Wang, Yan, *Data-Driven Distributionally Robust CVaR Portfolio Optimization under Regime-Switching Ambiguity Set*, SSRN 4378930, Theorem 1, display (12), p.13).

**Formalization Note** The "min" is an infimum in `EReal` over all feasible `(v, x, α, β)`;
it is `+∞` when the feasible set is empty (i.e. when `𝒳` is empty). -/
noncomputable def val12 {I K p q : ℕ} {N : Fin K → ℕ} (m : ℝ≥0∞)
    (r : (k : Fin K) → Fin (N k) → Fin I → ℝ) (w θ : Fin K → ℝ) (η : ℝ)
    (A : Matrix (Fin p) (Fin I) ℝ) (b : Fin p → ℝ) (C : Matrix (Fin q) (Fin I) ℝ)
    (d : Fin q → ℝ) : EReal :=
  ⨅ (v : ℝ) (x : Fin I → ℝ) (α : (k : Fin K) → Fin (N k) → ℝ) (β : ℝ)
    (_ : feas12 m r A b C d v x α β), ((obj12 w θ η v α β : ℝ) : EReal)

end RegimeDRCVaR


