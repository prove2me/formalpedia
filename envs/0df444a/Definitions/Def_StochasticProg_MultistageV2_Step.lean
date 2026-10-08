-- Prove2me | Definitions.Def_StochasticProg_MultistageV2_Step
-- name    : StochasticProg_MultistageV2_Step
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T20:53:45.746098+00:00
-- url     : https://prove2.me/theorems/c79f153d-d536-4ebf-94ec-345fb3988e9d
-- title:
--   One iteration of the nested L-shaped method
-- statement:
--   The transition relation $C\to C'$ of the nested L-shaped method on cut sets, with the order of visiting subproblems left free. (i) *Feasibility step* (Step 1): if a non-root node $k$ has $\mathrm{NLDS}(t,k)$ infeasible at a current solution $x_p$ of $a(k)$ and $(\pi,\rho)$ is a basic dual infeasibility certificate, the feasibility cut $\pi^{\top}T^{t-1}_k x\ge\pi^{\top}h^t_k+\rho^{\top}d_k$ is added to $a(k)$. (ii) *Optimality step* (Step 2): if $j$ has descendants, $(x_j,\theta_j)$ is a current solution of $j$, every descendant $k$ of $j$ is a leaf or already has an optimality cut, and $(\pi_k,\rho_k,\sigma_k)$ is an optimal basic dual solution of $\mathrm{NLDS}(k)$ at $x_j$ for each descendant, then the cut $Ex+\theta\ge e$ of Step 2 is added to $j$ provided $j$ has no optimality cut yet (so that it still carries $\theta_j=0$) or the cut is violated, $\bar\theta_j=e-Ex_j>\theta_j$.
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed. (2011), Ch. 6, §6.1, Steps 1–2 of the Nested L-Shaped Method, pp. 267–268 (PDF pp. 288–289); validity requirement from the proof of Theorem 1, p. 269

import Mathlib
import Definitions.Def_StochasticProg_Multistage_Tree
import Definitions.Def_StochasticProg_MultistageV2_Instance
import Definitions.Def_StochasticProg_MultistageV2_Cuts
import Definitions.Def_StochasticProg_MultistageV2_NLDSFeasible
import Definitions.Def_StochasticProg_MultistageV2_IsProposal
import Definitions.Def_StochasticProg_MultistageV2_IsInfeasibilityDualVertex
import Definitions.Def_StochasticProg_MultistageV2_feasCut
import Definitions.Def_StochasticProg_MultistageV2_IsOptimalDualVertex
import Definitions.Def_StochasticProg_MultistageV2_optCut

namespace StochasticProg.MultistageV2

variable {H n m : ℕ} {T : Multistage.Tree H}

open Classical in
/-- One cut-generating iteration of the nested L-shaped method (Steps 1–2, pp. 267–268),
with the order in which subproblems are visited left free ("Many alternative strategies are
possible in this algorithm in terms of determining the next subproblem (1.1)–(1.5) to
solve", p. 268). The state is the current cut set `C`.

* `feas` (Step 1, infeasible branch): a non-root node `k` whose subproblem NLDS(t,k) is
  infeasible at a current solution `xp` of its ancestor `a(k)`; a dual basic solution
  `(π, ρ)` certifying this yields the feasibility cut `feasCut` (`D = πᵀT`,
  `d = πᵀh + ρᵀd`), which is added to NLDS(t-1, a(k)).
* `opt` (Step 2): a node `j` with descendants, a current solution `(x_j, θ_j)` of NLDS(j),
  and for every descendant `k ∈ D(j)` an optimal dual basic solution `(π_k, ρ_k, σ_k)` of
  NLDS(k) at `x_j`; the cut `optCut` (`E`, `e` of p. 268, including the `ρ·d` and `σ·e`
  terms) is added to NLDS(j) if `j` still carries `θ_j = 0` (first cut, which removes that
  constraint) or if it is violated, `θ̄_j = e - E x_j > θ_j`. The duals of a descendant `k`
  that itself has descendants are used only once `k`'s placeholder `θ_k = 0` has been
  replaced by optimality cuts (`hready`): only then is NLDS(k) an outer linearisation of
  `k`'s subproblem, as the validity part of the proof of Theorem 1 requires (p. 269:
  "suppose the cuts in (1.3)–(1.4) are an outer linearization of `Q^{t+1}_k`"). -/
inductive Step (inst : Instance H n m T) : Cuts T n → Cuts T n → Prop
  | feas (C : Cuts T n) (k : T.Node) (hk : (T.stage k).val ≠ 0)
      (xp : Fin n → ℝ) (θp : ℝ) (hprop : IsProposal inst C (T.anc k) xp θp)
      (hinf : ¬ ∃ x θ, NLDSFeasible inst C k xp x θ)
      (π : Fin m → ℝ) (ρ : C.feas k → ℝ)
      (hdual : IsInfeasibilityDualVertex inst C k xp π ρ) :
      Step inst C
        ⟨Function.update C.feas (T.anc k) (insert (feasCut inst C k π ρ) (C.feas (T.anc k))),
          C.opt⟩
  | opt (C : Cuts T n) (j : T.Node) (hj : (T.children j).Nonempty)
      (xj : Fin n → ℝ) (θj : ℝ) (hprop : IsProposal inst C j xj θj)
      (hready : ∀ k ∈ T.children j, (T.children k).Nonempty → (C.opt k).Nonempty)
      (π : T.Node → Fin m → ℝ) (ρ : (k : T.Node) → C.feas k → ℝ)
      (σ : (k : T.Node) → C.opt k → ℝ)
      (hdual : ∀ k ∈ T.children j, IsOptimalDualVertex inst C k xj (π k) (ρ k) (σ k))
      (hcut : C.opt j = ∅ ∨
        θj < (optCut inst C j π ρ σ).2 - (optCut inst C j π ρ σ).1 ⬝ᵥ xj) :
      Step inst C
        ⟨C.feas, Function.update C.opt j (insert (optCut inst C j π ρ σ) (C.opt j))⟩

end StochasticProg.MultistageV2


