-- Prove2me | Definitions.Def_FirstOrderFG_Supplement_Alg1_runFrom
-- name    : FirstOrderFG_Supplement_Alg1_runFrom
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T03:40:53.680594+00:00
-- url     : https://prove2.me/theorems/8a417e9f-d54b-4a6f-80a5-fcfee3e7113a
-- title:
--   Algorithm 1 run from a specified round
-- statement:
--   Starting from a given Algorithm 1 state before global round $t$, this recursion applies one algorithm step for each arm in a supplied played-arm history, using the corresponding oblivious loss vectors.
--
--   It supplies the history-dependent state needed by the finite trajectory law.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Algorithm 1, p.7

import Mathlib
import Definitions.Def_FirstOrderFG_Supplement_Alg1_step

set_option autoImplicit false

namespace FirstOrderFG.Supplement

/-- **An Algorithm 1 instance run from global round `t` along a played-arm history.**
Zhang–Zhang–Luo–Mineiro, arXiv:2610.40861, Algorithm 1, p.7. -/
noncomputable def Alg1.runFrom {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E]
    (T : ℕ) (ℓ : ℕ → Fin K → ℝ) : ℕ → Alg1.State K → List (Fin K) → Alg1.State K
  | _, st, [] => st
  | t, st, I :: h => Alg1.runFrom E T ℓ (t + 1) (Alg1.step E T ℓ t st I) h

end FirstOrderFG.Supplement


