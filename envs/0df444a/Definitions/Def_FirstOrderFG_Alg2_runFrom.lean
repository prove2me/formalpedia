-- Prove2me | Definitions.Def_FirstOrderFG_Alg2_runFrom
-- name    : FirstOrderFG_Alg2_runFrom
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:53:28.946213+00:00
-- url     : https://prove2.me/theorems/4921e0b9-425b-40ef-9d85-010e9684fb57
-- title:
--   Run of an instance of Algorithm 2 on a sequence of arms
-- statement:
--   Starting from a state before global round $t$, the instance plays the arms of a list in rounds $t,t+1,\dots$; the result is the state after the last of them.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Algorithm 2, p.10

import Mathlib
import Definitions.Def_FirstOrderFG_Alg2_step

namespace FirstOrderFG

/-- **An instance of Algorithm 2 run from round `t` on a sequence of played arms.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861,
Algorithm 2, p.10.

`Alg2.runFrom E T ℓ q₀ t st h` is the state after the instance, in state `st` before global round `t`,
plays the arms of the list `h` in rounds `t, t+1, …`. -/
noncomputable def Alg2.runFrom {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E] (T : ℕ) (ℓ : ℕ → Fin K → ℝ)
    (q₀ : (Fin K → ℝ) → ℝ → Fin K → ℝ) : ℕ → Alg2.State K → List (Fin K) → Alg2.State K
  | _, st, [] => st
  | t, st, I :: h => Alg2.runFrom E T ℓ q₀ (t + 1) (Alg2.step E T ℓ q₀ t st I) h

end FirstOrderFG


