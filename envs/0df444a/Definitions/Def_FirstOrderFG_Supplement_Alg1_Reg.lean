-- Prove2me | Definitions.Def_FirstOrderFG_Supplement_Alg1_Reg
-- name    : FirstOrderFG_Supplement_Alg1_Reg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T03:45:34.402757+00:00
-- url     : https://prove2.me/theorems/c207fb3c-49d1-49f9-9786-1c4f9d8deebe
-- title:
--   Best-arm regret of Algorithm 1
-- statement:
--   Algorithm 1's best-arm expected regret is its expected incurred loss minus $L^\star=\min_kL_{T,k}$.
--
--   It is the regret used by the optimized conclusions of Theorem 3.2.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, §2, p.3; Theorem 3.2, p.7

import Mathlib
import Definitions.Def_FirstOrderFG_Supplement_Alg1_expLoss
import Definitions.Def_FirstOrderFG_Lstar

set_option autoImplicit false

namespace FirstOrderFG.Supplement

/-- **Algorithm 1's expected best-arm regret.** Zhang–Zhang–Luo–Mineiro,
arXiv:2610.40861, §2, p.3, and Theorem 3.2, p.7. -/
noncomputable def Alg1.Reg {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E]
    (T : ℕ) (ℓ : ℕ → Fin K → ℝ) (η : ℝ) : ℝ :=
  Alg1.expLoss E T ℓ η - FirstOrderFG.Lstar T ℓ

end FirstOrderFG.Supplement


