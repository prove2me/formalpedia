-- Prove2me | Definitions.Def_FirstOrderFG_RegK
-- name    : FirstOrderFG_RegK
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:02:44.066567+00:00
-- url     : https://prove2.me/theorems/a8790da0-8058-44ea-add4-6575d41bfa37
-- title:
--   Expected regret $\mathrm{Reg}_{T,k}$ against an action
-- statement:
--   The expected regret of Algorithm 4 against action $k$ is
--   $$
--   \mathrm{Reg}_{T,k}=\mathbb E\Big[\sum_{t=1}^T\ell_{t,I_t}\Big]-L_{T,k}.
--   $$
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, §2, p.3

import Mathlib
import Definitions.Def_FirstOrderFG_expLoss
import Definitions.Def_FirstOrderFG_Lk

namespace FirstOrderFG

/-- **The expected regret `Reg_{T,k}` of Algorithm 4 against action `k`.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, §2, p.3:
`Reg_{T,k} ≜ E[∑_{t=1}^T ℓ_{t,I_t}] − L_{T,k}`. -/
noncomputable def RegK {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E] (T : ℕ) (ℓ : ℕ → Fin K → ℝ)
    (q₀ : (Fin K → ℝ) → ℝ → Fin K → ℝ) (k : Fin K) : ℝ :=
  expLoss E T ℓ q₀ - Lk T ℓ k

end FirstOrderFG


