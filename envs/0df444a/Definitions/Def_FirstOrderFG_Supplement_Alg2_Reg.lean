-- Prove2me | Definitions.Def_FirstOrderFG_Supplement_Alg2_Reg
-- name    : FirstOrderFG_Supplement_Alg2_Reg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T03:49:07.378206+00:00
-- url     : https://prove2.me/theorems/4cf2a833-8dff-4b8c-9278-427d7e65ff85
-- title:
--   Best-arm regret of Algorithm 2
-- statement:
--   The published Algorithm 2 instance's best-arm expected regret is its expected incurred loss minus $L^\star$.
--
--   This is the regret appearing after the tuned choice of $\theta$ in Theorem 4.2.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, §2, p.3; Theorem 4.2, p.11

import Mathlib
import Definitions.Def_FirstOrderFG_Supplement_Alg2_expLoss
import Definitions.Def_FirstOrderFG_Lstar

set_option autoImplicit false

namespace FirstOrderFG.Supplement

/-- **Published Algorithm 2's expected best-arm regret.**
Zhang–Zhang–Luo–Mineiro, arXiv:2610.40861, §2, p.3, and Theorem 4.2, p.11. -/
noncomputable def Alg2.Reg {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E]
    (T : ℕ) (ℓ : ℕ → Fin K → ℝ) (q₀ : (Fin K → ℝ) → ℝ → Fin K → ℝ)
    (A θ : ℝ) : ℝ :=
  Alg2.expLoss E T ℓ q₀ A θ - FirstOrderFG.Lstar T ℓ

end FirstOrderFG.Supplement


