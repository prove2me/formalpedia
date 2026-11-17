-- Prove2me | Definitions.Def_FirstOrderFG_Supplement_Alg2_RegK
-- name    : FirstOrderFG_Supplement_Alg2_RegK
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T03:48:27.421324+00:00
-- url     : https://prove2.me/theorems/7de8cc09-94ab-425a-91d6-23e514a77f00
-- title:
--   Per-arm regret of Algorithm 2
-- statement:
--   Against arm $k$, the published Algorithm 2 instance with parameters $(A,\theta)$ has expected regret equal to its expected incurred loss minus $L_{T,k}$.
--
--   This is the left-hand side of Theorem 4.2.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, §2, p.3; Theorem 4.2, p.11

import Mathlib
import Definitions.Def_FirstOrderFG_Supplement_Alg2_expLoss
import Definitions.Def_FirstOrderFG_Lk

set_option autoImplicit false

namespace FirstOrderFG.Supplement

/-- **Published Algorithm 2's expected regret against arm `k`.**
Zhang–Zhang–Luo–Mineiro, arXiv:2610.40861, §2, p.3, and Theorem 4.2, p.11. -/
noncomputable def Alg2.RegK {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E]
    (T : ℕ) (ℓ : ℕ → Fin K → ℝ) (q₀ : (Fin K → ℝ) → ℝ → Fin K → ℝ)
    (A θ : ℝ) (k : Fin K) : ℝ :=
  Alg2.expLoss E T ℓ q₀ A θ - FirstOrderFG.Lk T ℓ k

end FirstOrderFG.Supplement


