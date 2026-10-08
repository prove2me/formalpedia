-- Prove2me | Definitions.Def_StochasticProg_MultistageV2_NLDSOptimal
-- name    : StochasticProg_MultistageV2_NLDSOptimal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T18:46:09.959073+00:00
-- url     : https://prove2.me/theorems/a451a436-fdbf-40e4-8bb5-aea295cdb201
-- title:
--   Optimal solution of the nested subproblem NLDS(t,k)
-- statement:
--   $(x,\theta)$ is an *optimal solution* of $\mathrm{NLDS}(t,k)$ (cut set $C$, ancestor decision $x_p$) if it is feasible for $\mathrm{NLDS}(t,k)$ and $(c^t_k)^{\top}x+\theta\le (c^t_k)^{\top}x'+\theta'$ for every feasible $(x',\theta')$, i.e. it minimises the objective (1.1).
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed. (2011), Ch. 6, §6.1, NLDS(t,k), (1.1)–(1.5), p. 267 (PDF p. 288)

import Mathlib
import Definitions.Def_StochasticProg_Multistage_Tree
import Definitions.Def_StochasticProg_MultistageV2_Instance
import Definitions.Def_StochasticProg_MultistageV2_Cuts
import Definitions.Def_StochasticProg_MultistageV2_NLDSFeasible

namespace StochasticProg.MultistageV2

variable {H n m : ℕ} {T : Multistage.Tree H}

/-- `(x, θ)` is an optimal solution of the current subproblem NLDS(t,k) at the ancestor's
decision `xp`: it is feasible for (1.2)–(1.5) and minimises the objective (1.1)
`(c^t_k)ᵀ x + θ` over all feasible `(x', θ')` (p. 267). -/
def NLDSOptimal (inst : Instance H n m T) (C : Cuts T n) (k : T.Node) (xp : Fin n → ℝ)
    (x : Fin n → ℝ) (θ : ℝ) : Prop :=
  NLDSFeasible inst C k xp x θ ∧
    ∀ x' θ', NLDSFeasible inst C k xp x' θ' → inst.c k ⬝ᵥ x + θ ≤ inst.c k ⬝ᵥ x' + θ'

end StochasticProg.MultistageV2


