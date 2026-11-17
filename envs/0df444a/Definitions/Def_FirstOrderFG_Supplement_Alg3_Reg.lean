-- Prove2me | Definitions.Def_FirstOrderFG_Supplement_Alg3_Reg
-- name    : FirstOrderFG_Supplement_Alg3_Reg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T04:00:17.23727+00:00
-- url     : https://prove2.me/theorems/492eb3f2-9e84-4442-a8a1-039f5046dbe0
-- title:
--   Best-arm regret of Algorithm 3
-- statement:
--   Algorithm 3's best-arm expected regret is its expected incurred loss minus $L^\star$.
--
--   It is the final quantity in Theorem A.2 and the algorithm receives neither $\alpha$ nor $L^\star$ as an input.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Theorem A.2, p.15

import Mathlib
import Definitions.Def_FirstOrderFG_Supplement_Alg3_expLoss
import Definitions.Def_FirstOrderFG_Lstar

set_option autoImplicit false

namespace FirstOrderFG.Supplement

/-- **Algorithm 3's expected best-arm regret.** Zhang–Zhang–Luo–Mineiro,
arXiv:2610.40861, Theorem A.2, p.15. -/
noncomputable def Alg3.Reg {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E]
    (T : ℕ) (ℓ : ℕ → Fin K → ℝ) : ℝ :=
  Alg3.expLoss E T ℓ - FirstOrderFG.Lstar T ℓ

end FirstOrderFG.Supplement


