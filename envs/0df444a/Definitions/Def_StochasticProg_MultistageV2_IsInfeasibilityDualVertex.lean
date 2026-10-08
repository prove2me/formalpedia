-- Prove2me | Definitions.Def_StochasticProg_MultistageV2_IsInfeasibilityDualVertex
-- name    : StochasticProg_MultistageV2_IsInfeasibilityDualVertex
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T19:32:04.422503+00:00
-- url     : https://prove2.me/theorems/6c3f9174-47f6-496e-b655-16beec213184
-- title:
--   Basic dual certificate of infeasibility of NLDS(t,k)
-- statement:
--   Let $D_k$, $d_k$ collect the feasibility cuts of node $k$ (stage $t$). A pair $(\pi,\rho)\in\mathbb{R}^m\times\mathbb{R}^{r_k}$ is a *basic dual infeasibility certificate* for $\mathrm{NLDS}(t,k)$ at ancestor decision $x_p$ if it is an extreme point of the polytope $\{(\pi,\rho): \pi^{\top}W^t+\rho^{\top}D_k\le 0,\ -1\le\pi\le 1,\ 0\le\rho\le 1\}$ (the dual of the phase-one problem) and $\pi^{\top}(h^t_k-T^{t-1}_k x_p)+\rho^{\top}d_k>0$.
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed. (2011), Ch. 6, §6.1, Step 1, infeasible case (and Exercise 1), p. 267 (PDF p. 288); phase-one normalisation as in §5.1

import Mathlib
import Definitions.Def_StochasticProg_Multistage_Tree
import Definitions.Def_StochasticProg_MultistageV2_Instance
import Definitions.Def_StochasticProg_MultistageV2_rhs
import Definitions.Def_StochasticProg_MultistageV2_Cuts

namespace StochasticProg.MultistageV2

variable {H n m : ℕ} {T : Multistage.Tree H}

/-- Step 1's infeasibility certificate for NLDS(t,k) at ancestor decision `xp` (p. 267, "see
Exercise 1"): `(π, ρ)` is a *dual basic solution* — an extreme point of the dual polytope of
the phase-one problem of (1.2), (1.3), (1.5),
`{(π, ρ) | πᵀ W^t + ρᵀ D^t_k ≤ 0, -1 ≤ π ≤ 1, 0 ≤ ρ ≤ 1}` (the normalisation of the
two-stage feasibility test, §5.1) — with `πᵀ(h^t_k - T^{t-1}_k xp) + ρᵀ d^t_k > 0`. Here `ρ`
is indexed by `k`'s current feasibility cuts `(D, d) ∈ C.feas k`. -/
def IsInfeasibilityDualVertex (inst : Instance H n m T) (C : Cuts T n) (k : T.Node)
    (xp : Fin n → ℝ) (π : Fin m → ℝ) (ρ : C.feas k → ℝ) : Prop :=
  (π, ρ) ∈ Set.extremePoints ℝ
      {z : (Fin m → ℝ) × (C.feas k → ℝ) |
        (∀ i, ∑ r, z.1 r * inst.W (T.stage k) r i + ∑ q, z.2 q * (q.1.1 i) ≤ 0) ∧
        (∀ r, -1 ≤ z.1 r ∧ z.1 r ≤ 1) ∧ (∀ q, 0 ≤ z.2 q ∧ z.2 q ≤ 1)} ∧
    0 < π ⬝ᵥ rhs inst k xp + ∑ q, ρ q * q.1.2

end StochasticProg.MultistageV2


