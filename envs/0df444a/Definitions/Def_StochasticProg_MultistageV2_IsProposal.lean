-- Prove2me | Definitions.Def_StochasticProg_MultistageV2_IsProposal
-- name    : StochasticProg_MultistageV2_IsProposal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T19:08:52.683226+00:00
-- url     : https://prove2.me/theorems/6af03cab-fdc3-4518-84ed-98d9ca6c0d17
-- title:
--   Current solution (proposal) of a node
-- statement:
--   Under a cut set $C$, $(x,\theta)$ is a *current solution* of node $j$ if either $j$ is the root and $(x,\theta)$ is optimal for $\mathrm{NLDS}(1)$, or $j$ is not the root and $(x,\theta)$ is optimal for $\mathrm{NLDS}(t,j)$ at some ancestor decision $x_p$ that is itself (with some $\theta_p$) a current solution of $a(j)$. These are the proposals produced by the forward passes of Step 1.
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed. (2011), Ch. 6, §6.1, Step 1 and 'x^{t-1}_{a(k)} is the current solution from that scenario', p. 267 (PDF p. 288)

import Mathlib
import Definitions.Def_StochasticProg_Multistage_Tree
import Definitions.Def_StochasticProg_MultistageV2_Instance
import Definitions.Def_StochasticProg_MultistageV2_Cuts
import Definitions.Def_StochasticProg_MultistageV2_NLDSOptimal

namespace StochasticProg.MultistageV2

variable {H n m : ℕ} {T : Multistage.Tree H}

/-- `(x, θ)` is a current solution ("proposal") of node `j` under the cuts `C`, as produced by
the forward passes of Step 1 (p. 267): it is an optimal solution of NLDS(1) at the root, and,
for a non-root node, an optimal solution of NLDS(t,j) at some current solution `xp` of the
ancestor `a(j)` ("`x^{t-1}_{a(k)}` is the current solution from that scenario", p. 267). -/
inductive IsProposal (inst : Instance H n m T) (C : Cuts T n) : T.Node → (Fin n → ℝ) → ℝ → Prop
  | root (x : Fin n → ℝ) (θ : ℝ) :
      NLDSOptimal inst C T.root 0 x θ → IsProposal inst C T.root x θ
  | child (j : T.Node) (hj : (T.stage j).val ≠ 0) (xp : Fin n → ℝ) (θp : ℝ)
      (x : Fin n → ℝ) (θ : ℝ) :
      IsProposal inst C (T.anc j) xp θp → NLDSOptimal inst C j xp x θ →
        IsProposal inst C j x θ

end StochasticProg.MultistageV2


