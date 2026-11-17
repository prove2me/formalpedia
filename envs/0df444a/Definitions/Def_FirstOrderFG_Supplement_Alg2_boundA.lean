-- Prove2me | Definitions.Def_FirstOrderFG_Supplement_Alg2_boundA
-- name    : FirstOrderFG_Supplement_Alg2_boundA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T03:49:47.78117+00:00
-- url     : https://prove2.me/theorems/22128054-f268-4716-9038-3b65bdb0b9cb
-- title:
--   Graph-bound choice for optimized Algorithm 2
-- statement:
--   When $V_{\mathrm{self}}$ is nonempty, the optimized Algorithm 2 guarantee uses the explicit Lemma 2.1 bound on $G_{\mathrm{self}}$; when it is empty and no meta-action exists, Theorem 4.2 takes $A=1$.
--
--   This definition records that case distinction exactly.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Theorem 4.2, p.11

import Mathlib
import Definitions.Def_FirstOrderFG_Vself
import Definitions.Def_FirstOrderFG_Supplement_alphaBound

set_option autoImplicit false

namespace FirstOrderFG.Supplement

/-- **The graph bound used in the optimized clause of Theorem 4.2.**
Zhang–Zhang–Luo–Mineiro, arXiv:2610.40861, Theorem 4.2, p.11: use the Lemma 2.1
bound on `G_self` when the meta-action exists, and take `A = 1` otherwise. -/
noncomputable def Alg2.boundA {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E]
    (T : ℕ) : ℝ :=
  if (FirstOrderFG.Vself E).Nonempty then alphaBound E T else 1

end FirstOrderFG.Supplement


