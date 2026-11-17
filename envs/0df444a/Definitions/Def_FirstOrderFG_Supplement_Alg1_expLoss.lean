-- Prove2me | Definitions.Def_FirstOrderFG_Supplement_Alg1_expLoss
-- name    : FirstOrderFG_Supplement_Alg1_expLoss
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T03:43:27.740196+00:00
-- url     : https://prove2.me/theorems/fd9e45df-afd1-40f3-8492-b11aecc1599f
-- title:
--   Expected whole-horizon loss of Algorithm 1
-- statement:
--   The expected incurred loss of Algorithm 1 is
--
--   $$
--   \mathbb E\!\left[\sum_{t=1}^T\ell_{t,I_t}\right],
--   $$
--
--   evaluated by the published finite trajectory recursion using Algorithm 1's conditional sampling law.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, §2, p.3; Algorithm 1, p.7

import Mathlib
import Definitions.Def_FirstOrderFG_Supplement_Alg1_play
import Definitions.Def_FirstOrderFG_treeExp
import Definitions.Def_FirstOrderFG_pathLoss

set_option autoImplicit false

namespace FirstOrderFG.Supplement

/-- **Algorithm 1's whole-horizon expected incurred loss.** Zhang–Zhang–Luo–Mineiro,
arXiv:2610.40861, §2, p.3, and Algorithm 1, p.7.

**Formalization Note.** Expectation is the published finite trajectory tree for the oblivious
loss sequence, over rounds `1, …, T`. -/
noncomputable def Alg1.expLoss {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E]
    (T : ℕ) (ℓ : ℕ → Fin K → ℝ) (η : ℝ) : ℝ :=
  FirstOrderFG.treeExp (Alg1.play E T ℓ η) T [] (FirstOrderFG.pathLoss ℓ 1)

end FirstOrderFG.Supplement


