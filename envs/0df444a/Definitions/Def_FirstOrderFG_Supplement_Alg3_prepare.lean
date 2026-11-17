-- Prove2me | Definitions.Def_FirstOrderFG_Supplement_Alg3_prepare
-- name    : FirstOrderFG_Supplement_Alg3_prepare
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T03:52:43.042198+00:00
-- url     : https://prove2.me/theorems/7c05fb97-5682-4d1f-bbf2-0fa0c1a3daa6
-- title:
--   Pre-sampling doubling loop of Algorithm 3
-- statement:
--   Before sampling a round, Algorithm 3 computes $q_t$ and, while $H^G(q_t)>A_m$, doubles the guess, resets $S$ to zero, starts Algorithm 1 afresh from the uniform distribution at the printed max-based rate, and recomputes $q_t$.
--
--   The returned state is the first one whose test passes.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Algorithm 3, lines 4–8, p.15

import Mathlib
import Definitions.Def_FirstOrderFG_Supplement_Alg3_State
import Definitions.Def_FirstOrderFG_Supplement_Alg3_doublingIndex
import Definitions.Def_FirstOrderFG_Supplement_Alg1_init
import Definitions.Def_FirstOrderFG_Supplement_Alg1_initialEta
import Definitions.Def_FirstOrderFG_Supplement_Alg1_qOf
import Definitions.Def_FirstOrderFG_Hgraph

set_option autoImplicit false

namespace FirstOrderFG.Supplement

/-- **Algorithm 3's pre-sampling while-loop.** Zhang–Zhang–Luo–Mineiro,
arXiv:2610.40861, Algorithm 3, lines 4–8, p.15. If the current `q_t` violates the
guess, repeatedly double `A`, reset `S`, and start a fresh uniformly initialized Algorithm 1
instance until the test passes. -/
noncomputable def Alg3.prepare {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E]
    (T : ℕ) (st : Alg3.State K) : Alg3.State K :=
  if st.A < FirstOrderFG.Hgraph E T (Alg1.qOf E T st.inst) then
    let A' := st.A * 2 ^ Alg3.doublingIndex E T st.A
    ⟨A', Alg1.init K (Alg1.initialEta K T A'), 0⟩
  else st

end FirstOrderFG.Supplement


