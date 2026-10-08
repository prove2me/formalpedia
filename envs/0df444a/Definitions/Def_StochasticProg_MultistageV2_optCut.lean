-- Prove2me | Definitions.Def_StochasticProg_MultistageV2_optCut
-- name    : StochasticProg_MultistageV2_optCut
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T20:35:50.771412+00:00
-- url     : https://prove2.me/theorems/292d2c9d-8994-48bb-add7-946d2dff98a0
-- title:
--   Optimality cut of Step 2
-- statement:
--   Given dual solutions $(\pi_k,\rho_k,\sigma_k)$ of the descendants $k\in D^t(j)$ of a node $j$ at stage $t-1$, the optimality cut for $\mathrm{NLDS}(t-1,j)$ is $E x+\theta\ge e$ with
--   $$E=\sum_{k\in D^t(j)}\frac{p^t_k}{p^{t-1}_j}\,\pi_k^{\top}T^{t-1}_k,\qquad e=\sum_{k\in D^t(j)}\frac{p^t_k}{p^{t-1}_j}\Big[\pi_k^{\top}h^t_k+\sum_{i=1}^{r_k}\rho_{k,i}\,d^t_{k,i}+\sum_{i=1}^{s_k}\sigma_{k,i}\,e^t_{k,i}\Big].$$
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed. (2011), Ch. 6, §6.1, Step 2, formulas for $E^{t-1}_j$ and $e^{t-1}_j$, p. 268 (PDF p. 289)

import Mathlib
import Definitions.Def_StochasticProg_Multistage_Tree
import Definitions.Def_StochasticProg_MultistageV2_Instance
import Definitions.Def_StochasticProg_MultistageV2_Cuts

namespace StochasticProg.MultistageV2

variable {H n m : ℕ} {T : Multistage.Tree H}

/-- The optimality cut of Step 2 (p. 268) for node `j` at stage `t-1`, built from the stored
duals `(π_k, ρ_k, σ_k)` of its descendants `k ∈ D^t(j)`:
`E^{t-1}_j = ∑_{k ∈ D^t(j)} (p^t_k / p^{t-1}_j) π_kᵀ T^{t-1}_k` and
`e^{t-1}_j = ∑_{k ∈ D^t(j)} (p^t_k / p^{t-1}_j) [π_kᵀ h^t_k + ∑_i ρ_{ki} d^t_{ki} + ∑_i σ_{ki} e^t_{ki}]`,
where `ρ_k`, `σ_k` run over `k`'s own feasibility and optimality cuts. The cut reads
`E x^{t-1}_j + θ^{t-1}_j ≥ e`. -/
noncomputable def optCut (inst : Instance H n m T) (C : Cuts T n) (j : T.Node)
    (π : T.Node → Fin m → ℝ) (ρ : (k : T.Node) → C.feas k → ℝ)
    (σ : (k : T.Node) → C.opt k → ℝ) : (Fin n → ℝ) × ℝ :=
  (fun i => ∑ k ∈ T.children j, (inst.p k / inst.p j) * ∑ r, π k r * inst.Tmat k r i,
   ∑ k ∈ T.children j, (inst.p k / inst.p j) *
      (π k ⬝ᵥ inst.h k + ∑ q, ρ k q * q.1.2 + ∑ q, σ k q * q.1.2))

end StochasticProg.MultistageV2


