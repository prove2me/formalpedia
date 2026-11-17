-- Prove2me | Definitions.Def_FirstOrderFG_Supplement_Alg3_run
-- name    : FirstOrderFG_Supplement_Alg3_run
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T03:55:38.416198+00:00
-- url     : https://prove2.me/theorems/f4724018-e85b-4518-96a3-e51901a8a5f8
-- title:
--   Algorithm 3 state after a history
-- statement:
--   From the printed initial state, this is Algorithm 3's state before the round following a given played-arm history from round $1$ onward.
--
--   The state is a deterministic function of the oblivious losses and observed sampled arms.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Algorithm 3, p.15

import Mathlib
import Definitions.Def_FirstOrderFG_Supplement_Alg3_runFrom
import Definitions.Def_FirstOrderFG_Supplement_Alg3_init

set_option autoImplicit false

namespace FirstOrderFG.Supplement

/-- **Algorithm 3's state before the round following a history.**
Zhang–Zhang–Luo–Mineiro, arXiv:2610.40861, Algorithm 3, p.15. -/
noncomputable def Alg3.run {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E]
    (T : ℕ) (ℓ : ℕ → Fin K → ℝ) (h : List (Fin K)) : Alg3.State K :=
  Alg3.runFrom E T ℓ 1 (Alg3.init K T) h

end FirstOrderFG.Supplement


