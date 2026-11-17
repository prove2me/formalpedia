-- Prove2me | Definitions.Def_FirstOrderFG_Supplement_Alg3_play
-- name    : FirstOrderFG_Supplement_Alg3_play
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T03:56:48.214375+00:00
-- url     : https://prove2.me/theorems/1ca5f426-93b0-44e1-9850-3e0fc36342b5
-- title:
--   Next-arm law of Algorithm 3
-- statement:
--   After any history, Algorithm 3 first completes all required graph-bound doublings and then samples from the approximate fixed-point distribution of the surviving Algorithm 1 instance.
--
--   This is the conditional next-arm law used in the finite trajectory tree.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Algorithm 3, lines 4–9, p.15

import Mathlib
import Definitions.Def_FirstOrderFG_Supplement_Alg3_run
import Definitions.Def_FirstOrderFG_Supplement_Alg3_prepare
import Definitions.Def_FirstOrderFG_Supplement_Alg1_qOf

set_option autoImplicit false

namespace FirstOrderFG.Supplement

/-- **The law of Algorithm 3's next sampled arm.** Zhang–Zhang–Luo–Mineiro,
arXiv:2610.40861, Algorithm 3, lines 4–9, p.15: first complete all `A`-doublings,
then use the surviving fresh-or-continuing Algorithm 1 instance's `q_t`. -/
noncomputable def Alg3.play {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E]
    (T : ℕ) (ℓ : ℕ → Fin K → ℝ) (h : List (Fin K)) : Fin K → ℝ :=
  Alg1.qOf E T (Alg3.prepare E T (Alg3.run E T ℓ h)).inst

end FirstOrderFG.Supplement


