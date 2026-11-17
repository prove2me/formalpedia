-- Prove2me | Definitions.Def_FirstOrderFG_Supplement_Alg1_play
-- name    : FirstOrderFG_Supplement_Alg1_play
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T03:42:28.837554+00:00
-- url     : https://prove2.me/theorems/5fd1b8ba-1d7c-4de0-beab-0987dee15242
-- title:
--   Next-arm law of Algorithm 1
-- statement:
--   After any played-arm history, the next arm of Algorithm 1 is drawn from the approximate fixed-point distribution $q_t$ computed from the current state.
--
--   This gives the conditional sampling law at every node of the finite trajectory tree.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Algorithm 1, lines 3–4, p.7

import Mathlib
import Definitions.Def_FirstOrderFG_Supplement_Alg1_run
import Definitions.Def_FirstOrderFG_Supplement_Alg1_qOf

set_option autoImplicit false

namespace FirstOrderFG.Supplement

/-- **The law of Algorithm 1's next sampled arm.** Zhang–Zhang–Luo–Mineiro,
arXiv:2610.40861, Algorithm 1, lines 3–4, p.7: after history `h`, draw from the
approximate fixed point computed from the current `p_t`. -/
noncomputable def Alg1.play {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E]
    (T : ℕ) (ℓ : ℕ → Fin K → ℝ) (η : ℝ) (h : List (Fin K)) : Fin K → ℝ :=
  Alg1.qOf E T (Alg1.run E T ℓ η h)

end FirstOrderFG.Supplement


