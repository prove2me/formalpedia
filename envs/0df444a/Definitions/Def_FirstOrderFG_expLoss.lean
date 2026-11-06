-- Prove2me | Definitions.Def_FirstOrderFG_expLoss
-- name    : FirstOrderFG_expLoss
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:00:30.536619+00:00
-- url     : https://prove2.me/theorems/9fc8ee86-0f48-42af-842e-a5dfd65479d7
-- title:
--   Expected loss of Algorithm 4
-- statement:
--   The expected cumulative loss of Algorithm 4 is
--   $$
--   \mathbb E\Big[\sum_{t=1}^T\ell_{t,I_t}\Big].
--   $$
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, §2, p.3

import Mathlib
import Definitions.Def_FirstOrderFG_Alg4_condExp
import Definitions.Def_FirstOrderFG_pathLoss

namespace FirstOrderFG

/-- **The expected loss `E[∑_{t=1}^T ℓ_{t,I_t}]` of Algorithm 4.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, §2, p.3. -/
noncomputable def expLoss {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E] (T : ℕ) (ℓ : ℕ → Fin K → ℝ)
    (q₀ : (Fin K → ℝ) → ℝ → Fin K → ℝ) : ℝ :=
  Alg4.condExp E T ℓ q₀ [] (pathLoss ℓ 1)

end FirstOrderFG


