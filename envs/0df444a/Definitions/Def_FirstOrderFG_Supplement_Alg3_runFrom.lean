-- Prove2me | Definitions.Def_FirstOrderFG_Supplement_Alg3_runFrom
-- name    : FirstOrderFG_Supplement_Alg3_runFrom
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T03:54:33.261804+00:00
-- url     : https://prove2.me/theorems/30a28fad-d1a3-47c6-8c88-b1aa3858420d
-- title:
--   Algorithm 3 run from a specified round
-- statement:
--   Starting from a supplied Algorithm 3 state before global round $t$, this recursion performs one complete Algorithm 3 transition for each sampled arm in a history.
--
--   It includes every pre-round doubling and every post-round loss restart.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Algorithm 3, p.15

import Mathlib
import Definitions.Def_FirstOrderFG_Supplement_Alg3_step

set_option autoImplicit false

namespace FirstOrderFG.Supplement

/-- **Algorithm 3 run from global round `t` along a played-arm history.**
Zhang–Zhang–Luo–Mineiro, arXiv:2610.40861, Algorithm 3, p.15. -/
noncomputable def Alg3.runFrom {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E]
    (T : ℕ) (ℓ : ℕ → Fin K → ℝ) : ℕ → Alg3.State K → List (Fin K) → Alg3.State K
  | _, st, [] => st
  | t, st, I :: h => Alg3.runFrom E T ℓ (t + 1) (Alg3.step E T ℓ t st I) h

end FirstOrderFG.Supplement


