-- Prove2me | Definitions.Def_FirstOrderFG_Supplement_Alg1_qOf
-- name    : FirstOrderFG_Supplement_Alg1_qOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T03:39:14.559099+00:00
-- url     : https://prove2.me/theorems/29b0014e-7644-41b2-ac3b-ebcba5925778
-- title:
--   Approximate fixed-point distribution of Algorithm 1
-- statement:
--   At each round, Algorithm 1 starts Picard iteration from the uniform distribution and repeatedly applies the smoothed fixed-point map (11) for the current $p_t$ and $\eta$ until the residual is at most $\varepsilon=1/(KT^2)$. The resulting interior distribution is $q_t$.
--
--   The uniform start is part of Algorithm 1 and is not an arbitrary input.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Algorithm 1, line 3, p.7

import Mathlib
import Definitions.Def_FirstOrderFG_Supplement_Alg1_State
import Definitions.Def_FirstOrderFG_picardFixed

set_option autoImplicit false

namespace FirstOrderFG.Supplement

/-- **Algorithm 1's sampling distribution.** Zhang–Zhang–Luo–Mineiro,
*Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861,
Algorithm 1, line 3, p.7: starting from the uniform distribution, Picard-iterate the
smoothed map (11) until the residual is at most `ε = 1/(KT²)`.

**Formalization Note.** Unlike published Algorithm 2, whose start is an admissible parameter,
Algorithm 1 uses the paper's prescribed uniform start on every round. -/
noncomputable def Alg1.qOf {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E]
    (T : ℕ) (st : Alg1.State K) : Fin K → ℝ :=
  FirstOrderFG.picardFixed E T st.p st.η (fun _ => 1 / (K : ℝ))

end FirstOrderFG.Supplement


