-- Prove2me | Definitions.Def_StochasticProg_MultistageV2_obj
-- name    : StochasticProg_MultistageV2_obj
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T17:23:26.86081+00:00
-- url     : https://prove2.me/theorems/3b2a0e8b-34a5-4d0b-8d11-8539386e14e0
-- title:
--   Expected cost of the deterministic equivalent
-- statement:
--   The objective of (3.4.1) at an assignment $(x_k)_k$ is the expected total cost $\sum_{k} p_k\,(c_k)^{\top}x_k$, the sum running over all nodes of the scenario tree.
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed. (2011), Ch. 6, §6.1, objective of (3.4.1), p. 267 (PDF p. 288); cf. (1.7), p. 270

import Mathlib
import Definitions.Def_StochasticProg_Multistage_Tree
import Definitions.Def_StochasticProg_MultistageV2_Instance

namespace StochasticProg.MultistageV2

variable {H n m : ℕ} {T : Multistage.Tree H}

/-- The objective of the deterministic equivalent (3.4.1) (p. 267; cf. (1.7), p. 270): the
expected total cost `∑_k p^t_k (c^t_k)ᵀ x^t_k` over all scenario nodes. -/
def obj (inst : Instance H n m T) (xs : T.Node → Fin n → ℝ) : ℝ :=
  ∑ k : T.Node, inst.p k * (inst.c k ⬝ᵥ xs k)

end StochasticProg.MultistageV2


