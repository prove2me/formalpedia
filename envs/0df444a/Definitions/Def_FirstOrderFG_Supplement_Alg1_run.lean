-- Prove2me | Definitions.Def_FirstOrderFG_Supplement_Alg1_run
-- name    : FirstOrderFG_Supplement_Alg1_run
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T03:41:43.153297+00:00
-- url     : https://prove2.me/theorems/3b17827c-9a0c-4654-819a-a8ab3f4323c6
-- title:
--   Algorithm 1 state after a history
-- statement:
--   For a learning rate $\eta$ and played-arm history from rounds $1$ onward, this is the Algorithm 1 state before the next round, beginning from the printed uniform initialization.
--
--   The construction makes the learner's state a deterministic function of the observed history and the fixed oblivious loss sequence.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Algorithm 1, p.7

import Mathlib
import Definitions.Def_FirstOrderFG_Supplement_Alg1_runFrom
import Definitions.Def_FirstOrderFG_Supplement_Alg1_init

set_option autoImplicit false

namespace FirstOrderFG.Supplement

/-- **Algorithm 1's state before the round following a history.** Zhang–Zhang–Luo–Mineiro,
arXiv:2610.40861, Algorithm 1, p.7. The history's arms are the draws in rounds
`1, …, h.length`. -/
noncomputable def Alg1.run {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E]
    (T : ℕ) (ℓ : ℕ → Fin K → ℝ) (η : ℝ) (h : List (Fin K)) : Alg1.State K :=
  Alg1.runFrom E T ℓ 1 (Alg1.init K η) h

end FirstOrderFG.Supplement


