-- Prove2me | Definitions.Def_FirstOrderFG_Supplement_Alg3_RegK
-- name    : FirstOrderFG_Supplement_Alg3_RegK
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T03:59:34.055206+00:00
-- url     : https://prove2.me/theorems/0eae1db4-c54b-46ee-9ddf-539e384d2d30
-- title:
--   Per-arm regret of Algorithm 3
-- statement:
--   Against arm $k$, Algorithm 3's expected regret is its expected incurred loss minus $L_{T,k}$.
--
--   Theorem A.2 gives a first-order guarantee for this quantity simultaneously for every arm.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Theorem A.2, p.15

import Mathlib
import Definitions.Def_FirstOrderFG_Supplement_Alg3_expLoss
import Definitions.Def_FirstOrderFG_Lk

set_option autoImplicit false

namespace FirstOrderFG.Supplement

/-- **Algorithm 3's expected regret against arm `k`.** Zhang–Zhang–Luo–Mineiro,
arXiv:2610.40861, Theorem A.2, p.15. -/
noncomputable def Alg3.RegK {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E]
    (T : ℕ) (ℓ : ℕ → Fin K → ℝ) (k : Fin K) : ℝ :=
  Alg3.expLoss E T ℓ - FirstOrderFG.Lk T ℓ k

end FirstOrderFG.Supplement


