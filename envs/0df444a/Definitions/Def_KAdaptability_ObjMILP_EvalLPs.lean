-- Prove2me | Definitions.Def_KAdaptability_ObjMILP_EvalLPs
-- name    : KAdaptability_ObjMILP_EvalLPs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T08:01:41.23315+00:00
-- url     : https://prove2.me/theorems/07a60bc7-4292-48dc-a3da-6abb06670751
-- title:
--   The epigraph LP and its dual evaluating the objective of 𝒫𝒪_K (proof of Theorem 2)
-- statement:
--   Fix the data of the problem, a number $K$ of policies, a first-stage decision $x\in\mathbb R^N$ and policies $y^1,\dots,y^K\in\mathbb R^M$. The proof of Theorem 2 evaluates the objective of $\mathcal{PO}_K$ by two linear programs.
--
--   The **epigraph LP** is
--   $$\begin{aligned}\text{maximize}\quad & \xi^\top Cx+\tau\\ \text{subject to}\quad & \xi\in\mathbb R^Q,\ \tau\in\mathbb R,\\ & A\xi\le b,\\ & \tau\le\xi^\top Qy^k\quad\forall k\in\mathcal K.\end{aligned}$$
--
--   Its **dual LP** is
--   $$\begin{aligned}\text{minimize}\quad & b^\top\alpha\\ \text{subject to}\quad & \alpha\in\mathbb R^R_+,\ \beta\in\mathbb R^K_+,\\ & A^\top\alpha=Cx+\sum_{k\in\mathcal K}\beta_kQy^k,\\ & e^\top\beta=1,\end{aligned}$$
--   where $e$ is the all-ones vector.
--
--   This definition provides the feasible sets of both programs and their optimal values. They are the intermediate objects through which the objective of $\mathcal{PO}_K$ becomes the linear objective $b^\top\alpha$ of the MILP (5).
--
--   **Formalization Note** The optimal value of the epigraph LP is a supremum in `EReal` ($-\infty$ if infeasible, $+\infty$ if unbounded); the optimal value of the dual is an infimum in `EReal` ($+\infty$ if infeasible).
-- source:
--   Hanasusanto, Kuhn, Wiesemann, K-Adaptability in Two-Stage Robust Binary Programming, preprint, Optimization Online 2014/03/4294 (revision of 2015-03-30), p. ec3 (PDF p. 37), Proof of Theorem 2 (the epigraph LP and its dual)

import Mathlib
import Definitions.Def_KAdaptability_ObjMILP_Problem

open Matrix

namespace KAdaptability.ObjMILP

variable {N M L nQ R : ℕ}

/-- Feasibility in the epigraph LP of the proof of Theorem 2 (p. ec3) for fixed `x` and
`y¹, …, y^K`: `ξ ∈ ℝ^Q`, `τ ∈ ℝ`, `Aξ ≤ b` and `τ ≤ ξ⊤Qy^k` for every `k`. -/
def Problem.EpiFeasible (P : Problem N M L nQ R) (K : ℕ) (ys : Fin K → Fin M → ℝ)
    (ξ : Fin nQ → ℝ) (τ : ℝ) : Prop :=
  P.A *ᵥ ξ ≤ P.b ∧ ∀ k, τ ≤ ξ ⬝ᵥ (P.Q *ᵥ ys k)

/-- The optimal value of the epigraph LP `maximize ξ⊤Cx + τ` over `EpiFeasible`, as a supremum
in `EReal` (`⊥` if infeasible, `⊤` if unbounded). -/
noncomputable def Problem.epiValue (P : Problem N M L nQ R) (K : ℕ) (x : Fin N → ℝ)
    (ys : Fin K → Fin M → ℝ) : EReal :=
  ⨆ (ξ : Fin nQ → ℝ) (τ : ℝ) (_ : P.EpiFeasible K ys ξ τ), ((ξ ⬝ᵥ (P.C *ᵥ x) + τ : ℝ) : EReal)

/-- Feasibility in the dual LP of the proof of Theorem 2 (p. ec3) for fixed `x` and
`y¹, …, y^K`: `α ∈ ℝ^R_+`, `β ∈ ℝ^K_+`, `A⊤α = Cx + Σ_k β_k Qy^k` and `e⊤β = 1`. -/
def Problem.DualFeasible (P : Problem N M L nQ R) (K : ℕ) (x : Fin N → ℝ)
    (ys : Fin K → Fin M → ℝ) (α : Fin R → ℝ) (β : Fin K → ℝ) : Prop :=
  0 ≤ α ∧ 0 ≤ β ∧
    P.Aᵀ *ᵥ α = P.C *ᵥ x + ∑ k, β k • (P.Q *ᵥ ys k) ∧
    (1 : Fin K → ℝ) ⬝ᵥ β = 1

/-- The optimal value of the dual LP `minimize b⊤α` over `DualFeasible`, as an infimum in
`EReal` (`⊤` if infeasible). -/
noncomputable def Problem.dualValue (P : Problem N M L nQ R) (K : ℕ) (x : Fin N → ℝ)
    (ys : Fin K → Fin M → ℝ) : EReal :=
  ⨅ (α : Fin R → ℝ) (β : Fin K → ℝ) (_ : P.DualFeasible K x ys α β), ((P.b ⬝ᵥ α : ℝ) : EReal)

end KAdaptability.ObjMILP


