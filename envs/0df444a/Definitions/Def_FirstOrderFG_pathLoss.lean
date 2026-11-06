-- Prove2me | Definitions.Def_FirstOrderFG_pathLoss
-- name    : FirstOrderFG_pathLoss
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:44:39.960219+00:00
-- url     : https://prove2.me/theorems/90ec2bd6-c092-4cc2-85d4-05ad4fedd745
-- title:
--   Incurred loss $\sum_t\ell_{t,I_t}$ of a play sequence
-- statement:
--   For arms $I_t,I_{t+1},\dots$ played in consecutive rounds starting at $t$, the incurred loss is $\sum_j\ell_{t+j,I_{t+j}}$.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, §2, p.3

import Mathlib

namespace FirstOrderFG

/-- **The incurred loss `∑_t ℓ_{t,I_t}` of a play sequence.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, §2, p.3.

`pathLoss ℓ t h` is `∑_j ℓ_{t+j, h_j}`: the arms of `h` are played in rounds `t, t+1, …`. -/
def pathLoss {K : ℕ} (ℓ : ℕ → Fin K → ℝ) : ℕ → List (Fin K) → ℝ
  | _, [] => 0
  | t, I :: h => ℓ t I + pathLoss ℓ (t + 1) h

end FirstOrderFG


