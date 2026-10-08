-- Prove2me | Definitions.Def_StochasticProg_MultistageV2_feasCut
-- name    : StochasticProg_MultistageV2_feasCut
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T19:53:52.945482+00:00
-- url     : https://prove2.me/theorems/e84bc193-e810-4a4b-a537-bf7a2bc51543
-- title:
--   Feasibility cut sent to the ancestor
-- statement:
--   From a dual solution $(\pi,\rho)$ of an infeasible $\mathrm{NLDS}(t,k)$, the feasibility cut added to $\mathrm{NLDS}(t-1,a(k))$ is $D x\ge d$ with $D=\pi^{\top}T^{t-1}_k$ and $d=\pi^{\top}h^t_k+\sum_i\rho_i\,d^t_{k,i}$, the sum running over the feasibility cuts $(D^t_{k,i},d^t_{k,i})$ of $k$.
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed. (2011), Ch. 6, §6.1, Step 1, formula for $D^{t-1}_{a(k)}, d^{t-1}_{a(k)}$, p. 267 (PDF p. 288)

import Mathlib
import Definitions.Def_StochasticProg_Multistage_Tree
import Definitions.Def_StochasticProg_MultistageV2_Instance
import Definitions.Def_StochasticProg_MultistageV2_Cuts

namespace StochasticProg.MultistageV2

variable {H n m : ℕ} {T : Multistage.Tree H}

/-- The feasibility cut of Step 1 (p. 267) sent from an infeasible NLDS(t,k) to its ancestor
`a(k)`, built from a dual solution `(π, ρ)`:
`D^{t-1}_{a(k)} = πᵀ T^{t-1}_k` and `d^{t-1}_{a(k)} = πᵀ h^t_k + ρᵀ d^t_k`, where `ρ` runs
over `k`'s own feasibility cuts `(D^t_k, d^t_k)`. The cut reads `D x^{t-1}_{a(k)} ≥ d`. -/
def feasCut (inst : Instance H n m T) (C : Cuts T n) (k : T.Node) (π : Fin m → ℝ)
    (ρ : C.feas k → ℝ) : (Fin n → ℝ) × ℝ :=
  (fun i => ∑ r, π r * inst.Tmat k r i, π ⬝ᵥ inst.h k + ∑ q, ρ q * q.1.2)

end StochasticProg.MultistageV2


