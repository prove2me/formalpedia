-- Prove2me | Definitions.Def_FirstOrderFG_Supplement_Alg3_State
-- name    : FirstOrderFG_Supplement_Alg3_State
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T03:50:47.651506+00:00
-- url     : https://prove2.me/theorems/28bb4f16-0460-4140-9bcc-366888a8b983
-- title:
--   State of Algorithm 3
-- statement:
--   Algorithm 3's state records the current graph-bound guess $A_m$, the current fresh or continuing Algorithm 1 instance, and the realized incurred-loss accumulator $S$ since the latest restart.
--
--   The meta-epoch and epoch counters are represented by the values that the pseudocode actually reads: $A_m$ and the current instance's learning rate.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Algorithm 3, p.15

import Mathlib
import Definitions.Def_FirstOrderFG_Supplement_Alg1_State

set_option autoImplicit false

namespace FirstOrderFG.Supplement

/-- **State of Algorithm 3 between rounds.** Zhang–Zhang–Luo–Mineiro,
*Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861,
Algorithm 3, p.15: the current guess `A_m`, current fresh-or-continuing Algorithm 1 instance,
and realized incurred-loss accumulator `S` since the most recent restart. -/
structure Alg3.State (K : ℕ) where
  A : ℝ
  inst : Alg1.State K
  S : ℝ

end FirstOrderFG.Supplement


