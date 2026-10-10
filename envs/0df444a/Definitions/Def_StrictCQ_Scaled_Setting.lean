-- Prove2me | Definitions.Def_StrictCQ_Scaled_Setting
-- name    : StrictCQ_Scaled_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T20:56:03.24298+00:00
-- url     : https://prove2.me/theorems/5f3178a4-8731-4bf1-87ef-bebb924a9c6e
-- title:
--   (1.1), (2.1), pp. 1–3 — smooth constraint system, feasible set and KKT points
-- statement:
--   Fix integers $n, m, p \ge 0$. A **constraint system** consists of functions $h_1,\dots,h_m : \mathbb R^n \to \mathbb R$ (equalities) and $g_1,\dots,g_p : \mathbb R^n \to \mathbb R$ (inequalities). Here $\mathbb R^n$ is the Euclidean space with inner product $\langle\cdot,\cdot\rangle$ and norm $\|\cdot\|$. The system is **of class $C^1$** when every $h_i$ and every $g_j$ is continuously differentiable on $\mathbb R^n$. The **feasible set** is
--
--   $$
--   \Omega = \{x \in \mathbb R^n : h_i(x) = 0 \ (i = 1,\dots,m),\ g_j(x) \le 0 \ (j = 1,\dots,p)\}.
--   $$
--
--   Given an objective $f : \mathbb R^n \to \mathbb R$, a point $x^*$ **satisfies KKT** for $f$ if there exist $\lambda \in \mathbb R^m$ and $\mu \in \mathbb R^p$ with $\mu_j \ge 0$ for all $j$, $\mu_j = 0$ whenever $g_j(x^*) \ne 0$, and
--
--   $$
--   \nabla f(x^*) + \sum_{i=1}^m \lambda_i \nabla h_i(x^*) + \sum_{j=1}^p \mu_j \nabla g_j(x^*) = 0 .
--   $$
--
--   These are the objects of problem (1.1), "minimize $f(x)$ subject to $h(x) = 0$, $g(x) \le 0$", and of the feasible sets (2.1) of Andreani, Martínez, Ramos and Silva. Every statement of the mission is about a fixed constraint system and a feasible point $x^*$.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`, and the vector-valued $h, g$ of the paper are index families over `Fin m`, `Fin p` (the paper's indices $1,\dots,m$ shifted to $0,\dots,m-1$). Gradients are Mathlib's `gradient`; under the $C^1$ hypothesis they are the true gradients. The objective is not part of the structure, because the mission's characterizations quantify over it. Feasibility of $x^*$ is a separate hypothesis, not part of KKT; complementarity is written as "$\mu_j = 0$ off the active set".
-- source:
--   Andreani, Martínez, Ramos & Silva, Strict constraint qualifications and sequential optimality conditions for constrained optimization, Optimization Online 5197 (version of November 12, 2015), pp. 1–3, (1.1), (2.1), notation p. 3

import Mathlib

open Filter Topology

namespace StrictCQ.Scaled

/-- The constraint data `h : ℝⁿ → ℝᵐ`, `g : ℝⁿ → ℝᵖ` of problem (1.1)/(2.1), as index families. -/
structure Constraints (n m p : ℕ) where
  h : Fin m → EuclideanSpace ℝ (Fin n) → ℝ
  g : Fin p → EuclideanSpace ℝ (Fin n) → ℝ

namespace Constraints

variable {n m p : ℕ} (C : Constraints n m p)

/-- Standing hypothesis of p. 1: every `hᵢ` and every `gⱼ` is continuously differentiable. -/
def IsC1 : Prop :=
  (∀ i, ContDiff ℝ 1 (C.h i)) ∧ ∀ j, ContDiff ℝ 1 (C.g j)

/-- The feasible set `Ω = {x : h(x) = 0, g(x) ≤ 0}` of (2.1). -/
def feasible : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | (∀ i, C.h i x = 0) ∧ ∀ j, C.g j x ≤ 0}

/-- KKT at `xs` for the objective `f`, in multiplier form (feasibility is a separate hypothesis). -/
def IsKKT (f : EuclideanSpace ℝ (Fin n) → ℝ) (xs : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ (lam : Fin m → ℝ) (mu : Fin p → ℝ), (∀ j, 0 ≤ mu j) ∧ (∀ j, C.g j xs ≠ 0 → mu j = 0) ∧
    gradient f xs + ∑ i, lam i • gradient (C.h i) xs + ∑ j, mu j • gradient (C.g j) xs = 0

end Constraints

end StrictCQ.Scaled


