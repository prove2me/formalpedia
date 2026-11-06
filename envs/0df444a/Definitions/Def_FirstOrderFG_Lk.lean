-- Prove2me | Definitions.Def_FirstOrderFG_Lk
-- name    : FirstOrderFG_Lk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:44:55.899429+00:00
-- url     : https://prove2.me/theorems/b1854929-3c52-4206-9dc3-5a1c1d0a1622
-- title:
--   Cumulative loss $L_{T,k}$ of a fixed action
-- statement:
--   For a fixed action $k$, $L_{T,k}=\sum_{t=1}^T\ell_{t,k}$.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, §2, p.3

import Mathlib

namespace FirstOrderFG

/-- **The cumulative loss `L_{T,k} = ∑_{t=1}^T ℓ_{t,k}` of a fixed action.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, §2, p.3
(`L_{T,k} ≜ L_T(e_k)`, `L_T(u) ≜ ∑_t ⟨u, ℓ_t⟩`). Rounds are `t ∈ {1, …, T}`. -/
def Lk {K : ℕ} (T : ℕ) (ℓ : ℕ → Fin K → ℝ) (k : Fin K) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T, ℓ t k

end FirstOrderFG


