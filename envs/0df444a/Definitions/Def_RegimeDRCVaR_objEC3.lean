-- Prove2me | Definitions.Def_RegimeDRCVaR_objEC3
-- name    : RegimeDRCVaR_objEC3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:22:39.670676+00:00
-- url     : https://prove2.me/theorems/4348cf8f-ce98-46fb-a920-2d3ffcdf6578
-- title:
--   Objective of the dual (EC.3)
-- statement:
--   The objective of the dual problem (EC.3) is
--   $$
--   \sum_{k\in[K]}\sum_{n\in[N_k]}\frac{w_k}{N_k}\alpha_{nk}+\sum_{k\in[K]}\beta_k w_k\theta_k .
--   $$
--   It also appears inside the bracket of the objective of (EC.7).
-- source:
--   Pun, Wang, Yan, Data-Driven Distributionally Robust CVaR Portfolio Optimization under Regime-Switching Ambiguity Set, SSRN 4378930, proof of Theorem 1, display (EC.3), p.ec2

import Mathlib

namespace RegimeDRCVaR

/-- **The objective of the dual problem (EC.3)**
`∑_{k∈[K]} ∑_{n∈[N_k]} (w_k/N_k) α_{nk} + ∑_{k∈[K]} β_k w_kθ_k`
(Pun, Wang, Yan, *Data-Driven Distributionally Robust CVaR Portfolio Optimization under Regime-Switching Ambiguity Set*, SSRN 4378930, proof of Theorem 1, display (EC.3), p.ec2). -/
noncomputable def objEC3 {K : ℕ} {N : Fin K → ℕ} (w θ : Fin K → ℝ)
    (α : (k : Fin K) → Fin (N k) → ℝ) (β : Fin K → ℝ) : ℝ :=
  (∑ k, ∑ n, w k / (N k : ℝ) * α k n) + ∑ k, β k * w k * θ k

end RegimeDRCVaR


