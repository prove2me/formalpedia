-- Prove2me | Definitions.Def_KAdaptability_ObjMILP_MILP5
-- name    : KAdaptability_ObjMILP_MILP5
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T07:59:53.79398+00:00
-- url     : https://prove2.me/theorems/ea6a9ff3-3d24-4fb4-b6bf-2c015d235caa
-- title:
--   The mixed-integer linear program (5) of Theorem 2
-- statement:
--   Fix the data of the problem and a number $K$ of policies, $\mathcal K=\{1,\dots,K\}$, and let $e$ denote the all-ones vector of the appropriate dimension. The **MILP (5)** is
--   $$\begin{aligned}\text{minimize}\quad & b^\top\alpha\\ \text{subject to}\quad & x\in\mathcal X,\ y^k\in\mathcal Y,\ k\in\mathcal K,\\ & z^k\in\mathbb R^M_+,\ k\in\mathcal K,\ \alpha\in\mathbb R^R_+,\ \beta\in\mathbb R^K_+,\\ & A^\top\alpha=Cx+\sum_{k\in\mathcal K}Qz^k,\quad e^\top\beta=1,\\ & Tx+Wy^k\le h,\ \ z^k\le y^k,\ \ z^k\le\beta_ke,\ \ z^k\ge(\beta_k-1)e+y^k\quad\forall k\in\mathcal K.\end{aligned}$$
--
--   This definition provides:
--   1. feasibility of a point $(x,y^1,\dots,y^K,z^1,\dots,z^K,\alpha,\beta)$ in (5);
--   2. for fixed $(x,y^1,\dots,y^K)$, the infimum of $b^\top\alpha$ over all $(z,\alpha,\beta)$ that complete it to a feasible point of (5);
--   3. the optimal value of (5), the infimum of $b^\top\alpha$ over all feasible points.
--
--   The variables $z^k$ stand for the products $\beta_ky^k$; the three inequalities on $z^k$ are their exact linearization when $y^k$ is binary.
--
--   **Formalization Note** Values are infima in `EReal`; an empty infimum is $+\infty$. The constraint $Tx+Wy^k\le h$ is part of (5), exactly as on p. 13.
-- source:
--   Hanasusanto, Kuhn, Wiesemann, K-Adaptability in Two-Stage Robust Binary Programming, preprint, Optimization Online 2014/03/4294 (revision of 2015-03-30), p. 13, Theorem 2, problem (5)

import Mathlib
import Definitions.Def_KAdaptability_ObjMILP_Problem

open Matrix

namespace KAdaptability.ObjMILP

variable {N M L nQ R : ℕ}

/-- Feasibility of `(x, y¹, …, y^K, z¹, …, z^K, α, β)` in the MILP (5) of Theorem 2 (p. 13):
`x ∈ 𝒳`, `y^k ∈ 𝒴`, `z^k ∈ ℝ^M_+`, `α ∈ ℝ^R_+`, `β ∈ ℝ^K_+`, `A⊤α = Cx + Σ_k Qz^k`, `e⊤β = 1`,
and for every `k`: `Tx + Wy^k ≤ h`, `z^k ≤ y^k`, `z^k ≤ β_k e`, `z^k ≥ (β_k − 1)e + y^k`.
Here `e = 1` is the all-ones vector of the appropriate dimension. -/
def Problem.MILPFeasible (P : Problem N M L nQ R) (K : ℕ) (x : Fin N → ℝ)
    (ys : Fin K → Fin M → ℝ) (zs : Fin K → Fin M → ℝ) (α : Fin R → ℝ) (β : Fin K → ℝ) :
    Prop :=
  x ∈ P.X ∧ (∀ k, ys k ∈ P.Y) ∧ (∀ k, 0 ≤ zs k) ∧ 0 ≤ α ∧ 0 ≤ β ∧
    P.Aᵀ *ᵥ α = P.C *ᵥ x + ∑ k, P.Q *ᵥ zs k ∧
    (1 : Fin K → ℝ) ⬝ᵥ β = 1 ∧
    ∀ k, P.T *ᵥ x + P.W *ᵥ ys k ≤ P.h ∧
      zs k ≤ ys k ∧ zs k ≤ β k • (1 : Fin M → ℝ) ∧
      (β k - 1) • (1 : Fin M → ℝ) + ys k ≤ zs k

/-- The value of (5) with the binary decisions `(x, y¹, …, y^K)` fixed: the infimum of `b⊤α` over
the `(z, α, β)` that complete them to a feasible point of (5), in `EReal` (`⊤` if none does). -/
noncomputable def Problem.milpValueAt (P : Problem N M L nQ R) (K : ℕ) (x : Fin N → ℝ)
    (ys : Fin K → Fin M → ℝ) : EReal :=
  ⨅ (zs : Fin K → Fin M → ℝ) (α : Fin R → ℝ) (β : Fin K → ℝ)
    (_ : P.MILPFeasible K x ys zs α β), ((P.b ⬝ᵥ α : ℝ) : EReal)

/-- The optimal value of the MILP (5): the infimum of `b⊤α` over all its feasible points, in
`EReal` (`⊤` if (5) is infeasible). -/
noncomputable def Problem.optMILP (P : Problem N M L nQ R) (K : ℕ) : EReal :=
  ⨅ (x : Fin N → ℝ) (ys : Fin K → Fin M → ℝ) (zs : Fin K → Fin M → ℝ) (α : Fin R → ℝ)
    (β : Fin K → ℝ) (_ : P.MILPFeasible K x ys zs α β), ((P.b ⬝ᵥ α : ℝ) : EReal)

end KAdaptability.ObjMILP


