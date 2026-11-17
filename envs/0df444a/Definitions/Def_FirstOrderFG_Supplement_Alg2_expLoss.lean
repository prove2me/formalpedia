-- Prove2me | Definitions.Def_FirstOrderFG_Supplement_Alg2_expLoss
-- name    : FirstOrderFG_Supplement_Alg2_expLoss
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T03:47:56.17212+00:00
-- url     : https://prove2.me/theorems/508ec6a9-5ddc-4756-b56f-632cdafb6b3b
-- title:
--   Expected whole-horizon loss of Algorithm 2
-- statement:
--   Initialize the published Algorithm 2 with graph $G$, horizon $T$, graph bound $A$, and master rate $\theta$. Its expected whole-horizon loss is
--
--   $$
--   \mathbb E\!\left[\sum_{t=1}^T\ell_{t,I_t}\right].
--   $$
--
--   This definition reuses the published initialization, transition, play distribution, and finite-tree expectation unchanged.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Algorithm 2, pp.8–11; §2, p.3

import Mathlib
import Definitions.Def_FirstOrderFG_Alg2_condExp
import Definitions.Def_FirstOrderFG_Alg2_init
import Definitions.Def_FirstOrderFG_pathLoss

set_option autoImplicit false

namespace FirstOrderFG.Supplement

/-- **Whole-horizon expected loss of the published Algorithm 2.**
Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*,
arXiv:2610.40861, Algorithm 2, pp.8–11, and §2, p.3.

The instance is initialized with `(A,θ)` before round `1` and the published conditional
finite-tree expectation is evaluated through round `T`; Algorithm 2 itself is not duplicated
or altered. -/
noncomputable def Alg2.expLoss {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E]
    (T : ℕ) (ℓ : ℕ → Fin K → ℝ) (q₀ : (Fin K → ℝ) → ℝ → Fin K → ℝ)
    (A θ : ℝ) : ℝ :=
  FirstOrderFG.Alg2.condExp E T ℓ q₀ 1 (FirstOrderFG.Alg2.init E A θ)
    (FirstOrderFG.pathLoss ℓ 1)

end FirstOrderFG.Supplement


