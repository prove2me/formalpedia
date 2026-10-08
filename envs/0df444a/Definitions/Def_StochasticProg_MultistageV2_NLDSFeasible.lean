-- Prove2me | Definitions.Def_StochasticProg_MultistageV2_NLDSFeasible
-- name    : StochasticProg_MultistageV2_NLDSFeasible
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T18:22:24.111012+00:00
-- url     : https://prove2.me/theorems/048a8619-624a-4c26-9377-18450302ca26
-- title:
--   Feasible point of the nested subproblem NLDS(t,k)
-- statement:
--   Given a cut set $C$, a node $k$ at stage $t$ and an ancestor decision $x_p$, a pair $(x,\theta)\in\mathbb{R}^n\times\mathbb{R}$ is *feasible for* $\mathrm{NLDS}(t,k)$ if $x\ge 0$, $W^t x = h^t_k - T^{t-1}_k x_p$ (resp. $h^1$ at the root), $Dx\ge d$ for every feasibility cut $(D,d)$ of $k$, $Ex+\theta\ge e$ for every optimality cut $(E,e)$ of $k$, and $\theta=0$ if $k$ has no optimality cut.
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed. (2011), Ch. 6, §6.1, NLDS(t,k), (1.2)–(1.5), and Step 0, p. 267 (PDF p. 288)

import Mathlib
import Definitions.Def_StochasticProg_Multistage_Tree
import Definitions.Def_StochasticProg_MultistageV2_Instance
import Definitions.Def_StochasticProg_MultistageV2_rhs
import Definitions.Def_StochasticProg_MultistageV2_Cuts

namespace StochasticProg.MultistageV2

variable {H n m : ℕ} {T : Multistage.Tree H}

/-- `(x, θ)` is feasible for the current subproblem NLDS(t,k), (1.2)–(1.5), p. 267, at the
ancestor's current decision `xp = x^{t-1}_{a(k)}`: `x ≥ 0` (1.5),
`W^t x = h^t_k - T^{t-1}_k xp` (1.2), every feasibility cut `D x ≥ d` of `k` (1.3), every
optimality cut `E x + θ ≥ e` of `k` (1.4), and Step 0's `θ = 0` while `k` has no optimality
cut yet (p. 267; this also covers the stage-`H` problem, which has no `θ`). -/
def NLDSFeasible (inst : Instance H n m T) (C : Cuts T n) (k : T.Node) (xp : Fin n → ℝ)
    (x : Fin n → ℝ) (θ : ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧
    (inst.W (T.stage k)).mulVec x = rhs inst k xp ∧
    (∀ q ∈ C.feas k, q.2 ≤ q.1 ⬝ᵥ x) ∧
    (∀ q ∈ C.opt k, q.2 ≤ q.1 ⬝ᵥ x + θ) ∧
    (C.opt k = ∅ → θ = 0)

end StochasticProg.MultistageV2


