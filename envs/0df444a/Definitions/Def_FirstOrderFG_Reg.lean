-- Prove2me | Definitions.Def_FirstOrderFG_Reg
-- name    : FirstOrderFG_Reg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:02:25.514556+00:00
-- url     : https://prove2.me/theorems/0f42ca0c-cb5c-4844-b5f8-ee20c4ba0aec
-- title:
--   Expected regret $\mathrm{Reg}_T$
-- statement:
--   The expected regret of Algorithm 4 against the best fixed action is
--   $$
--   \mathrm{Reg}_T=\max_{k\in[K]}\mathrm{Reg}_{T,k}=\mathbb E\Big[\sum_{t=1}^T\ell_{t,I_t}\Big]-L^\star .
--   $$
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, §2, p.3

import Mathlib
import Definitions.Def_FirstOrderFG_expLoss
import Definitions.Def_FirstOrderFG_Lstar

namespace FirstOrderFG

/-- **The expected regret `Reg_T` of Algorithm 4.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, §2, p.3:
`Reg_T ≜ max_k Reg_{T,k} = E[∑_{t=1}^T ℓ_{t,I_t}] − L⋆`. -/
noncomputable def Reg {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E] (T : ℕ) (ℓ : ℕ → Fin K → ℝ)
    (q₀ : (Fin K → ℝ) → ℝ → Fin K → ℝ) : ℝ :=
  expLoss E T ℓ q₀ - Lstar T ℓ

end FirstOrderFG


