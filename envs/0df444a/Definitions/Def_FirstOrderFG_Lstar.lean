-- Prove2me | Definitions.Def_FirstOrderFG_Lstar
-- name    : FirstOrderFG_Lstar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:46:29.613536+00:00
-- url     : https://prove2.me/theorems/576bdcd7-572d-47e3-86e7-60549276fead
-- title:
--   Loss of the best action $L^\star$
-- statement:
--   $L^\star=\min_{k\in[K]}L_{T,k}$.
--
--   **Formalization Note** The infimum over the finite set of arms is attained when $K\ge1$.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, §2, p.3

import Mathlib
import Definitions.Def_FirstOrderFG_Lk

namespace FirstOrderFG

/-- **The loss of the best fixed action `L⋆ = min_k L_{T,k}`.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, §2, p.3.

**Formalization Note.** The infimum over the finite type `Fin K` is attained (a minimum) when
`K ≥ 1`; every theorem assumes `K ≥ 2`. -/
noncomputable def Lstar {K : ℕ} (T : ℕ) (ℓ : ℕ → Fin K → ℝ) : ℝ :=
  ⨅ k, Lk T ℓ k

end FirstOrderFG


