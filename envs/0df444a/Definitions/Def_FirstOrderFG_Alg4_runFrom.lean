-- Prove2me | Definitions.Def_FirstOrderFG_Alg4_runFrom
-- name    : FirstOrderFG_Alg4_runFrom
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:55:07.038663+00:00
-- url     : https://prove2.me/theorems/ae267f89-679b-464e-b337-d7af0b0a44a2
-- title:
--   Run of Algorithm 4 on a sequence of arms
-- statement:
--   Starting from a state before round $t$, Algorithm 4 plays the arms of a list in rounds $t,t+1,\dots$.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Algorithm 4, p.32

import Mathlib
import Definitions.Def_FirstOrderFG_Alg4_step

namespace FirstOrderFG

/-- **Algorithm 4 run from round `t` on a sequence of played arms.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, Algorithm 4, p.32. -/
noncomputable def Alg4.runFrom {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E] (T : ℕ) (ℓ : ℕ → Fin K → ℝ)
    (q₀ : (Fin K → ℝ) → ℝ → Fin K → ℝ) : ℕ → Alg4.State K → List (Fin K) → Alg4.State K
  | _, st, [] => st
  | t, st, I :: h => Alg4.runFrom E T ℓ q₀ (t + 1) (Alg4.step E T ℓ q₀ t st I) h

end FirstOrderFG


