-- Prove2me | Definitions.Def_StochasticProg_MultistageV2_IsOptimalDualVertex
-- name    : StochasticProg_MultistageV2_IsOptimalDualVertex
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T20:18:35.155485+00:00
-- url     : https://prove2.me/theorems/686c8e23-c9fe-4304-8162-bec8639e941d
-- title:
--   Optimal basic dual solution of NLDS(t,k)
-- statement:
--   Let $(D_{k,i},d_{k,i})_{i\le r_k}$ and $(E_{k,i},e_{k,i})_{i\le s_k}$ be the cuts of node $k$ (stage $t$). A triple $(\pi,\rho,\sigma)$ is an *optimal basic dual solution* of $\mathrm{NLDS}(t,k)$ at ancestor decision $x_p$ if it is an extreme point of the dual feasible region $\{\pi^{\top}W^t+\rho^{\top}D_k+\sigma^{\top}E_k\le (c^t_k)^{\top},\ \rho\ge 0,\ \sigma\ge 0,\ \sum_i\sigma_i=1\}$ (the last equation only when $s_k\ge 1$; otherwise $\theta_k=0$ and $\sigma$ is void) and its dual objective $\pi^{\top}(h^t_k-T^{t-1}_kx_p)+\rho^{\top}d_k+\sigma^{\top}e_k$ equals $(c^t_k)^{\top}x+\theta$ for some feasible point $(x,\theta)$ of $\mathrm{NLDS}(t,k)$; by weak duality both are then optimal.
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed. (2011), Ch. 6, §6.1, Step 1, feasible case ('complementary basic dual multipliers on constraints (1.2)–(1.4)'), p. 267 (PDF p. 288)

import Mathlib
import Definitions.Def_StochasticProg_Multistage_Tree
import Definitions.Def_StochasticProg_MultistageV2_Instance
import Definitions.Def_StochasticProg_MultistageV2_rhs
import Definitions.Def_StochasticProg_MultistageV2_Cuts
import Definitions.Def_StochasticProg_MultistageV2_NLDSFeasible

namespace StochasticProg.MultistageV2

variable {H n m : ℕ} {T : Multistage.Tree H}

/-- Step 1's stored dual for a feasible NLDS(t,k) at ancestor decision `xp` (p. 267, "store
the value of the complementary basic dual multipliers on constraints (1.2)–(1.4) as
`(π^t_k, ρ^t_k, σ^t_k)`"): `(π, ρ, σ)` is an extreme point (basic solution) of the dual
feasible region of (1.1)–(1.5),
`{πᵀ W^t + ρᵀ D^t_k + σᵀ E^t_k ≤ (c^t_k)ᵀ, ρ ≥ 0, σ ≥ 0, ∑ σ = 1}` (the last equation is the
dual constraint of the free variable `θ^t_k`, absent while `θ^t_k = 0`, i.e. while `k` has no
optimality cut), and it is optimal: its dual objective
`πᵀ(h^t_k - T^{t-1}_k xp) + ρᵀ d^t_k + σᵀ e^t_k` equals the objective value of a feasible
point of NLDS(t,k) (so, by weak duality, both are optimal). -/
def IsOptimalDualVertex (inst : Instance H n m T) (C : Cuts T n) (k : T.Node)
    (xp : Fin n → ℝ) (π : Fin m → ℝ) (ρ : C.feas k → ℝ) (σ : C.opt k → ℝ) : Prop :=
  (π, ρ, σ) ∈ Set.extremePoints ℝ
      {z : (Fin m → ℝ) × (C.feas k → ℝ) × (C.opt k → ℝ) |
        (∀ q, 0 ≤ z.2.1 q) ∧ (∀ q, 0 ≤ z.2.2 q) ∧
        (∀ i, ∑ r, z.1 r * inst.W (T.stage k) r i + ∑ q, z.2.1 q * (q.1.1 i) +
            ∑ q, z.2.2 q * (q.1.1 i) ≤ inst.c k i) ∧
        ((C.opt k).Nonempty → ∑ q, z.2.2 q = 1)} ∧
    ∃ x θ, NLDSFeasible inst C k xp x θ ∧
      inst.c k ⬝ᵥ x + θ = π ⬝ᵥ rhs inst k xp + ∑ q, ρ q * q.1.2 + ∑ q, σ q * q.1.2

end StochasticProg.MultistageV2


