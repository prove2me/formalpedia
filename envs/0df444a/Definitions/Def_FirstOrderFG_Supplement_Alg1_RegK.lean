-- Prove2me | Definitions.Def_FirstOrderFG_Supplement_Alg1_RegK
-- name    : FirstOrderFG_Supplement_Alg1_RegK
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T03:44:12.207451+00:00
-- url     : https://prove2.me/theorems/ba7f73c4-4a92-47cc-ba19-431a912b6f86
-- title:
--   Per-arm regret of Algorithm 1
-- statement:
--   Against a fixed arm $k$, Algorithm 1's expected regret is
--
--   $$
--   \operatorname{Reg}^{\mathrm{Alg1}}_{T,k}=\mathbb E\!\left[\sum_{t=1}^T\ell_{t,I_t}\right]-L_{T,k}.
--   $$
--
--   This is the quantity bounded exactly in Theorem 3.2.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, §2, p.3; Theorem 3.2, p.7

import Mathlib
import Definitions.Def_FirstOrderFG_Supplement_Alg1_expLoss
import Definitions.Def_FirstOrderFG_Lk

set_option autoImplicit false

namespace FirstOrderFG.Supplement

/-- **Algorithm 1's expected regret against arm `k`.** Zhang–Zhang–Luo–Mineiro,
arXiv:2610.40861, §2, p.3, and Theorem 3.2, p.7. -/
noncomputable def Alg1.RegK {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E]
    (T : ℕ) (ℓ : ℕ → Fin K → ℝ) (η : ℝ) (k : Fin K) : ℝ :=
  Alg1.expLoss E T ℓ η - FirstOrderFG.Lk T ℓ k

end FirstOrderFG.Supplement


