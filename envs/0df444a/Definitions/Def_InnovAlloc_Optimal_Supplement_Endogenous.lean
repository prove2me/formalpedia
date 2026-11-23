-- Prove2me | Definitions.Def_InnovAlloc_Optimal_Supplement_Endogenous
-- name    : InnovAlloc_Optimal_Supplement_Endogenous
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T09:47:32.581625+00:00
-- url     : https://prove2.me/theorems/91563e82-e2f7-4c88-877d-77a21c38d5b5
-- title:
--   §4.1, p. 18 — joint optimality over common sharing rates and feasible allocations
-- statement:
--   The principal chooses a common profit share $\gamma\in(0,1)$ and nonnegative resource allocations $b_1,b_2$ whose sum is at most capacity $B$. The agents then play the published effort game. A candidate is jointly optimal if it is admissible, has an effort equilibrium, and
--
--   $$\Pi(\eta,c_1,c_2;z_1,z_2)\le\Pi(\gamma,b_1,b_2;x_1,x_2)$$
--
--   for every candidate equilibrium $(x_1,x_2)$, every alternative common share $\eta\in(0,1)$, every feasible split $(c_1,c_2)$, and every equilibrium $(z_1,z_2)$ at that alternative. Here $\Pi$ is the published principal profit, with $\alpha\in[0,1]$ determining profit when both products succeed.
--
--   This extends fixed-share optimality to the principal's joint control problem. No threshold or closed-form allocation is built into optimality. Capacity is positive in its applications. The zero-profit regime $0<B\le1$ is retained separately in Theorem 2.
--
--   **Formalization Note** The every-equilibrium convention is inherited from the published base model, including the multiplicity possible at $\alpha=0$.
-- source:
--   Gao, Fan, Huang & Chen, “Resource Allocation Among Competing Innovators”, SSRN preprint 3658157 (February 2021), p. 18, §4.1 and footnote 10

import Mathlib
import Definitions.Def_InnovAlloc_Optimal_Model

namespace InnovAlloc.Optimal.Supplement

/-- Joint choice of the common share and allocation (§4.1, p. 18).
Every candidate equilibrium dominates every equilibrium at every feasible alternative share/split. -/
def IsJointOptimal (α B γ b1 b2 : ℝ) : Prop :=
  γ ∈ Set.Ioo (0 : ℝ) 1 ∧ Feasible B b1 b2 ∧
    (∃ x1 x2, IsEquilibrium α γ b1 b2 x1 x2) ∧
    ∀ x1 x2, IsEquilibrium α γ b1 b2 x1 x2 →
      ∀ η ∈ Set.Ioo (0 : ℝ) 1, ∀ c1 c2, Feasible B c1 c2 →
        ∀ z1 z2, IsEquilibrium α η c1 c2 z1 z2 →
          principalProfit α η c1 c2 z1 z2 ≤ principalProfit α γ b1 b2 x1 x2

end InnovAlloc.Optimal.Supplement


