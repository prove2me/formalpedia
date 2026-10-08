-- Prove2me | Definitions.Def_ALADIN_LocalStab_Decoupled
-- name    : ALADIN_LocalStab_Decoupled
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:46:41.634054+00:00
-- url     : https://prove2.me/theorems/47774103-e343-4ef7-80f6-72437aeed118
-- title:
--   The decoupled subproblems (3.2) = (7.1) of ALADIN: $\min_{\xi} f_i(\xi)+\lambda^\top A_i\xi+\frac\rho2\|\xi-x_i\|_{\Sigma_i}^2$ s.t. $h_i(\xi)\le0$
-- statement:
--   Let problem (1.1) be given with data $f_i, h_i, A_i, b$. In step 1 of Algorithm 2 (ALADIN), given a primal iterate $x=(x_1,\dots,x_N)\in\mathbb R^{Nn}$, a dual iterate $\lambda\in\mathbb R^m$, a penalty parameter $\rho$ and scaling matrices $\Sigma_i\in\mathbb R^{n\times n}$, each agent $i$ solves the **decoupled problem**
--
--   $$
--   \min_{\xi\in\mathbb R^n}\ \varphi_i(x,\lambda;\xi) := f_i(\xi) + \lambda^\top A_i\xi + \frac{\rho}{2}\,\|\xi - x_i\|_{\Sigma_i}^2 \qquad\text{s.t.}\qquad h_i(\xi)\le 0,
--   $$
--
--   where $\|v\|_{\Sigma}^2 = v^\top\Sigma v$. This is problem (3.2) of the paper, written again as (7.1) in the proof of Lemma 3 with the variable named $\xi_i$.
--
--   A **local minimizer** of the decoupled problem for block $i$ with parameters $(x,\lambda)$ is a point $\xi$ with $h_i(\xi)\le 0$ such that $\varphi_i(x,\lambda;\xi)\le\varphi_i(x,\lambda;\eta)$ for every feasible $\eta$ in some neighbourhood of $\xi$. The paper's step 1 allows the subproblems to be solved "to either local or global optimality", and Lemma 3 is about locally unique local minimizers.
--
--   The decoupled problems are the only nonlinear, nonconvex computations of ALADIN, and they run in parallel across agents; their local behaviour as $(x,\lambda)$ moves near a solution is what the local convergence analysis of §7 controls.
--
--   **Formalization Note** Vectors are `Fin n → ℝ`; $\lambda^\top A_i\xi$ is `lam ⬝ᵥ (A i *ᵥ ξ)` and $\|v\|^2_{\Sigma_i}$ is `v ⬝ᵥ (Σ i *ᵥ v)`. The local-minimizer predicate `IsDecoupledLocalMin` requires feasibility of $\xi$ explicitly, because Mathlib's `IsLocalMinOn` alone holds vacuously at infeasible points (the feasible set is closed).
-- source:
--   Houska, Frasch, Diehl, An augmented Lagrangian based algorithm for distributed nonconvex optimization, SIAM J. Optim. 26 (2016), p. 1108, Algorithm 2 step 1, (3.2); p. 1117, (7.1)

import Mathlib
import Definitions.Def_ALADIN_LocalStab_Problem

namespace ALADIN.LocalStab

open Matrix

variable {N n m nh : ℕ}

/-- The objective of the decoupled problem (3.2) of Algorithm 2, step 1 (p. 1108), = (7.1) (p. 1117),
for block `i` with parameters `x ∈ ℝ^{N·n}`, `λ ∈ ℝᵐ`, penalty `ρ` and scaling matrix `Σᵢ`:
`ξ ↦ fᵢ(ξ) + λᵀ Aᵢ ξ + (ρ/2) ‖ξ − xᵢ‖²_{Σᵢ}`, where `‖v‖²_Σ = vᵀ Σ v`. -/
noncomputable def decoupledObjective (P : Problem N n m nh) (ρ : ℝ) (Sig : Fin N → Matrix (Fin n) (Fin n) ℝ)
    (x : Fin N → Fin n → ℝ) (lam : Fin m → ℝ) (i : Fin N) (ξ : Fin n → ℝ) : ℝ :=
  P.f i ξ + lam ⬝ᵥ (P.A i *ᵥ ξ) + ρ / 2 * ((ξ - x i) ⬝ᵥ (Sig i *ᵥ (ξ - x i)))

/-- The feasible set `{ξ ∈ ℝⁿ | hᵢ(ξ) ≤ 0}` of the decoupled problem (3.2) / (7.1) for block `i`. -/
def decoupledFeasibleSet (P : Problem N n m nh) (i : Fin N) : Set (Fin n → ℝ) :=
  {ξ | ∀ j, P.h i ξ j ≤ 0}

/-- `ξ` is a **local minimizer** of the decoupled problem (3.2) / (7.1) for block `i` with parameters
`(x, λ)`: `ξ` is feasible (`hᵢ(ξ) ≤ 0`) and the objective at `ξ` is `≤` its value at every feasible
point of some neighbourhood of `ξ`. (Feasibility is stated explicitly: Mathlib's `IsLocalMinOn` alone
holds vacuously at infeasible points, since the feasible set is closed for continuous `hᵢ`.) -/
def IsDecoupledLocalMin (P : Problem N n m nh) (ρ : ℝ) (Sig : Fin N → Matrix (Fin n) (Fin n) ℝ)
    (x : Fin N → Fin n → ℝ) (lam : Fin m → ℝ) (i : Fin N) (ξ : Fin n → ℝ) : Prop :=
  ξ ∈ decoupledFeasibleSet P i ∧
    IsLocalMinOn (decoupledObjective P ρ Sig x lam i) (decoupledFeasibleSet P i) ξ

end ALADIN.LocalStab


