-- Prove2me | Definitions.Def_FirstOrderFG_Supplement_Alg1_State
-- name    : FirstOrderFG_Supplement_Alg1_State
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T03:37:54.361269+00:00
-- url     : https://prove2.me/theorems/33864f79-4cf1-415d-a6f2-687b47530aa8
-- title:
--   State of Algorithm 1
-- statement:
--   The state of one Algorithm 1 instance consists of its fixed learning rate $\eta$ and its current EXP3 distribution $p_t$ on the ordinary probability simplex $\Delta_K$.
--
--   It is the state carried between played rounds; the sampling distribution $q_t$ is recomputed from $p_t$ each round.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Algorithm 1, p.7

import Mathlib

set_option autoImplicit false

namespace FirstOrderFG.Supplement

/-- **State of Algorithm 1 between rounds.** Zhang–Zhang–Luo–Mineiro,
*Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861,
Algorithm 1, p.7: the fixed learning rate `η` and the current ordinary-simplex EXP3
distribution `p_t`. -/
structure Alg1.State (K : ℕ) where
  η : ℝ
  p : Fin K → ℝ

end FirstOrderFG.Supplement


