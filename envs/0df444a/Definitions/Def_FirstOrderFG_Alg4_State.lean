-- Prove2me | Definitions.Def_FirstOrderFG_Alg4_State
-- name    : FirstOrderFG_Alg4_State
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:46:25.093816+00:00
-- url     : https://prove2.me/theorems/a7e40be1-7260-4656-930d-f0b464613733
-- title:
--   State of Algorithm 4
-- statement:
--   Algorithm 4 (the doubling trick) keeps the current instance of Algorithm 2, whose inputs are the current guess $A_m$ and master rate $\theta_{m,\lambda}$, and the accumulated observable loss $S$ since the last restart.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Algorithm 4, p.32

import Mathlib
import Definitions.Def_FirstOrderFG_Alg2_State

namespace FirstOrderFG

/-- **The state of Algorithm 4 between rounds.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, Algorithm 4, p.32: the current instance
of Algorithm 2 (which carries the guess `A_m` and the master rate `θ_{m,λ}` as its inputs) and the
accumulated observable loss `S` since the last restart.

**Formalization Note.** The counters `m`, `λ` are not stored: no line of Algorithm 4 reads them
except through `A_m` and `θ_{m,λ}`. -/
structure Alg4.State (K : ℕ) where
  inst : Alg2.State K
  S : ℝ

end FirstOrderFG


