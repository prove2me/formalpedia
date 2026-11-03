-- Prove2me | Definitions.Def_RegimeDRCVaR_obj12
-- name    : RegimeDRCVaR_obj12
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:22:40.09488+00:00
-- url     : https://prove2.me/theorems/3fe01290-8184-465d-925f-a77d97d2bf98
-- title:
--   Objective of problem (12)
-- statement:
--   The objective of problem (12) is
--   $$
--   J_{12}(v,\boldsymbol\alpha,\beta)=v+\frac{1}{1-\eta}\Big[\sum_{k\in[K]}\sum_{n\in[N_k]}\frac{w_k}{N_k}\alpha_{nk}+\beta\sum_{k\in[K]}w_k\theta_k\Big].
--   $$
--   The first sum is the empirical CVaR term over the pooled samples; the second is the price $\beta\ge\|x\|_{m^*}$ of the total transport budget $\sum_k w_k\theta_k$.
-- source:
--   Pun, Wang, Yan, Data-Driven Distributionally Robust CVaR Portfolio Optimization under Regime-Switching Ambiguity Set, SSRN 4378930, Theorem 1, display (12), p.13

import Mathlib

namespace RegimeDRCVaR

/-- **The objective of problem (12)**
`v + (1 − η)⁻¹ [∑_{k∈[K]} ∑_{n∈[N_k]} (w_k/N_k) α_{nk} + β ∑_{k∈[K]} w_kθ_k]`
(Pun, Wang, Yan, *Data-Driven Distributionally Robust CVaR Portfolio Optimization under Regime-Switching Ambiguity Set*, SSRN 4378930, Theorem 1, display (12), p.13). -/
noncomputable def obj12 {K : ℕ} {N : Fin K → ℕ} (w θ : Fin K → ℝ) (η : ℝ) (v : ℝ)
    (α : (k : Fin K) → Fin (N k) → ℝ) (β : ℝ) : ℝ :=
  v + (1 - η)⁻¹ * ((∑ k, ∑ n, w k / (N k : ℝ) * α k n) + β * ∑ k, w k * θ k)

end RegimeDRCVaR


