-- Prove2me | Definitions.Def_StochasticProg_MultistageV2_Feasible
-- name    : StochasticProg_MultistageV2_Feasible
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T17:03:02.896701+00:00
-- url     : https://prove2.me/theorems/8b86ca4f-5a44-40c0-b8dc-f5dd000a5fde
-- title:
--   Feasibility for the deterministic equivalent
-- statement:
--   An assignment $(x_k)_{k}$ of decisions to all nodes of the scenario tree is *feasible* for the deterministic equivalent (3.4.1) if for every node $k$ at stage $t$, $x_k\ge 0$ and $W^t x_k = h^t_k - T^{t-1}_k x_{a(k)}$ (with right-hand side $h^1$ at the root).
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed. (2011), Ch. 6, §6.1, problem (3.4.1) as used on p. 267 (PDF p. 288); cf. (1.7), p. 270

import Mathlib
import Definitions.Def_StochasticProg_Multistage_Tree
import Definitions.Def_StochasticProg_MultistageV2_Instance
import Definitions.Def_StochasticProg_MultistageV2_rhs

namespace StochasticProg.MultistageV2

variable {H n m : ℕ} {T : Multistage.Tree H}

/-- Feasibility for the deterministic equivalent (3.4.1) (§3.4, used in §6.1, p. 267): an
assignment `xs` of a decision to every scenario node with `xs k ≥ 0` and
`W^t xs k = h^t_k - T^{t-1}_k xs (a(k))` at every node `k` (constraints (1.2), (1.5) without
any cuts). -/
def Feasible (inst : Instance H n m T) (xs : T.Node → Fin n → ℝ) : Prop :=
  ∀ k : T.Node, (∀ i, 0 ≤ xs k i) ∧
    (inst.W (T.stage k)).mulVec (xs k) = rhs inst k (xs (T.anc k))

end StochasticProg.MultistageV2


