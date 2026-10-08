-- Prove2me | Definitions.Def_StochasticProg_MultistageV2_Cuts_empty
-- name    : StochasticProg_MultistageV2_Cuts_empty
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T18:04:18.794896+00:00
-- url     : https://prove2.me/theorems/90984991-4d04-4aa1-a623-89f0633d109f
-- title:
--   Initial cut set (Step 0)
-- statement:
--   The initial state of the nested L-shaped method (Step 0): $r^t_k=s^t_k=0$ for all $t,k$, i.e. no feasibility and no optimality cuts at any node.
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed. (2011), Ch. 6, §6.1, Step 0, p. 267 (PDF p. 288)

import Mathlib
import Definitions.Def_StochasticProg_Multistage_Tree
import Definitions.Def_StochasticProg_MultistageV2_Cuts

namespace StochasticProg.MultistageV2

/-- The initial state of Step 0 (p. 267): `r^t_k = s^t_k = 0`, no feasibility or
optimality cuts at any node (so every NLDS(t,k) carries `θ^t_k = 0`). -/
def Cuts.empty {H : ℕ} (T : Multistage.Tree H) (n : ℕ) : Cuts T n :=
  ⟨fun _ => ∅, fun _ => ∅⟩

end StochasticProg.MultistageV2


