-- Prove2me | Definitions.Def_FirstOrderFG_Supplement_Alg3_doublingIndex
-- name    : FirstOrderFG_Supplement_Alg3_doublingIndex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T03:52:02.892966+00:00
-- url     : https://prove2.me/theorems/ecbb1cae-41e8-4696-b109-954309f1daea
-- title:
--   Number of pre-round $A$-doublings in Algorithm 3
-- statement:
--   If the current guess fails $H^G(q_t)\le A$, Algorithm 3 doubles $A$ and starts a fresh Algorithm 1 instance repeatedly. The doubling index is the first $j\ge1$ for which the fresh instance at guess $A2^j$ passes the test.
--
--   This permits several doublings before one sampled round and therefore permits empty meta-epochs.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Algorithm 3, lines 5–8, p.15

import Mathlib
import Definitions.Def_FirstOrderFG_Supplement_Alg1_init
import Definitions.Def_FirstOrderFG_Supplement_Alg1_initialEta
import Definitions.Def_FirstOrderFG_Supplement_Alg1_qOf
import Definitions.Def_FirstOrderFG_Hgraph

set_option autoImplicit false

namespace FirstOrderFG.Supplement

/-- **Number of consecutive `A`-doublings before one sampled round of Algorithm 3.**
Zhang–Zhang–Luo–Mineiro, arXiv:2610.40861, Algorithm 3, lines 5–8, p.15.
It is the first `j ≥ 1` for which the fresh Algorithm 1 instance at guess `A·2^j`
passes `H^G(q_t) ≤ A·2^j`.

**Formalization Note.** The `sInf` models the while-loop, including empty intermediate
meta-epochs. The set is nonempty because the paper proves `H^G(q) ≤ K`. -/
noncomputable def Alg3.doublingIndex {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E]
    (T : ℕ) (A : ℝ) : ℕ :=
  sInf {j : ℕ | 1 ≤ j ∧
    FirstOrderFG.Hgraph E T
      (Alg1.qOf E T
        (Alg1.init K (Alg1.initialEta K T (A * 2 ^ j)))) ≤ A * 2 ^ j}

end FirstOrderFG.Supplement


