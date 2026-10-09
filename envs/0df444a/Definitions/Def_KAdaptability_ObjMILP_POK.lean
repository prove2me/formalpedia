-- Prove2me | Definitions.Def_KAdaptability_ObjMILP_POK
-- name    : KAdaptability_ObjMILP_POK
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T07:59:53.915099+00:00
-- url     : https://prove2.me/theorems/66da5a1a-7c5a-4c4d-a155-961c5d449937
-- title:
--   The K-adaptability problem 𝒫𝒪_K: objective, feasible decisions and optimal value
-- statement:
--   Fix the data of the two-stage robust binary program with objective uncertainty and a number $K$ of second-stage policies, indexed by $\mathcal K=\{1,\dots,K\}$. The **K-adaptability problem** $\mathcal{PO}_K$ (Observation 1 of the paper) is
--   $$\begin{aligned}\text{minimize}\quad & \max_{\xi\in\Xi}\Big[\xi^\top Cx+\min_{k\in\mathcal K}\xi^\top Qy^k\Big]\\ \text{subject to}\quad & x\in\mathcal X,\ y^k\in\mathcal Y,\ k\in\mathcal K,\\ & Tx+Wy^k\le h\quad\forall k\in\mathcal K.\end{aligned}$$
--
--   This definition provides three objects:
--   1. the objective $\Phi(x,\{y^k\})=\sup_{\xi\in\Xi}\big[\xi^\top Cx+\min_{k}\xi^\top Qy^k\big]$ at any decision $(x,y^1,\dots,y^K)$;
--   2. feasibility of a decision: $x\in\mathcal X$, and $y^k\in\mathcal Y$, $Tx+Wy^k\le h$ for every $k$;
--   3. the optimal value: the infimum of $\Phi$ over the feasible decisions.
--
--   The first-stage decision $x$ and the $K$ candidate policies are chosen here and now; after $\xi$ is revealed, the best of the $K$ policies is selected.
--
--   **Formalization Note** All values are extended reals (`EReal`), following the paper's convention (p. 10) that max and min stand for sup and inf when not attained. The optimal value of an infeasible problem is $+\infty$ (the infimum of the empty set). Policies are indexed by `Fin K` and need not be distinct.
-- source:
--   Hanasusanto, Kuhn, Wiesemann, K-Adaptability in Two-Stage Robust Binary Programming, preprint, Optimization Online 2014/03/4294 (revision of 2015-03-30), p. 10 (problem (3)), p. 11 (Observation 1, problem (PO_K))

import Mathlib
import Definitions.Def_KAdaptability_ObjMILP_Problem

open Matrix

namespace KAdaptability.ObjMILP

variable {N M L nQ R : ℕ}

/-- The objective of the K-adaptability problem 𝒫𝒪_K (Observation 1, p. 11) at a decision
`(x, y¹, …, y^K)`: `sup_{ξ∈Ξ} [ξ⊤Cx + min_{k∈𝒦} ξ⊤Qy^k]`, in `EReal`. The policies are indexed
by `Fin K` and need not be distinct. -/
noncomputable def Problem.objPOK (P : Problem N M L nQ R) (K : ℕ) (x : Fin N → ℝ)
    (ys : Fin K → Fin M → ℝ) : EReal :=
  ⨆ ξ ∈ P.Xi, (((ξ ⬝ᵥ (P.C *ᵥ x) : ℝ) : EReal) + ⨅ k, ((ξ ⬝ᵥ (P.Q *ᵥ ys k) : ℝ) : EReal))

/-- Feasibility in 𝒫𝒪_K: `x ∈ 𝒳`, and every policy satisfies `y^k ∈ 𝒴` and `Tx + Wy^k ≤ h`. -/
def Problem.FeasibleK (P : Problem N M L nQ R) (K : ℕ) (x : Fin N → ℝ)
    (ys : Fin K → Fin M → ℝ) : Prop :=
  x ∈ P.X ∧ ∀ k, ys k ∈ P.Y ∧ P.T *ᵥ x + P.W *ᵥ ys k ≤ P.h

/-- The optimal value of 𝒫𝒪_K: the infimum of `objPOK` over the feasible decisions
(`⊤` if there are none). -/
noncomputable def Problem.optPOK (P : Problem N M L nQ R) (K : ℕ) : EReal :=
  ⨅ (x : Fin N → ℝ) (ys : Fin K → Fin M → ℝ) (_ : P.FeasibleK K x ys), P.objPOK K x ys

end KAdaptability.ObjMILP


