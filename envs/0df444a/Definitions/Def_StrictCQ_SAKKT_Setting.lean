-- Prove2me | Definitions.Def_StrictCQ_SAKKT_Setting
-- name    : StrictCQ_SAKKT_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T23:31:14.907315+00:00
-- url     : https://prove2.me/theorems/a8ec0045-8d3d-4367-945c-67d086ab22a0
-- title:
--   (1.1), (3.7), (4.2), pp. 1–6 — constraint system, KKT, linearized cone, Ω(x, γ)
-- statement:
--   This file fixes the objects of the nonlinear program
--
--   $$
--   \min f(x)\quad\text{subject to}\quad h(x)=0,\ g(x)\le 0, \tag{1.1}
--   $$
--
--   with $h:\mathbb R^n\to\mathbb R^m$ and $g:\mathbb R^n\to\mathbb R^p$, on which every statement of the mission is built.
--
--   1. **Constraint data.** The components $h_1,\dots,h_m$ and $g_1,\dots,g_p$ are real functions on $\mathbb R^n$ (Euclidean space, inner product $\langle\cdot,\cdot\rangle$). The standing hypothesis $\mathrm{C}^1$ says that each component is continuously differentiable. The feasible set is $\Omega=\{x : h(x)=0,\ g(x)\le 0\}$, and $J(x^*)=\{j : g_j(x^*)=0\}$ is the set of active inequality constraints.
--   2. **KKT.** For an objective $f$, the KKT condition holds at $x^*$ if there are $\lambda\in\mathbb R^m$ and $\mu\in\mathbb R^p_+$ with $\mu_j=0$ for $j\notin J(x^*)$ and
--   $$\nabla f(x^*)+\sum_{i=1}^m\lambda_i\nabla h_i(x^*)+\sum_{j=1}^p\mu_j\nabla g_j(x^*)=0.$$
--   3. **Linearized cone (3.7)** $L_\Omega(x^*)=\{d : \langle\nabla h_i(x^*),d\rangle=0\ \forall i,\ \langle\nabla g_j(x^*),d\rangle\le0\ \forall j\in J(x^*)\}$.
--   4. **The linearized sets (4.2).** For $\gamma\in[-\infty,0]$,
--   $$\Omega(x,\gamma)=\left\{z:\ \begin{array}{ll}\langle\nabla h_i(x),z-x\rangle=0, & \text{for all } i\\ \langle\nabla g_j(x),z-x\rangle\le0, & \text{if } 0\le g_j(x)\\ g_j(x)+\langle\nabla g_j(x),z-x\rangle\le 0, & \text{if } \gamma<g_j(x)<0\end{array}\right\}.$$
--   At $\gamma=0$ the third family of rows is empty, so $\Omega(x,0)$ keeps the equality rows and the rows of the inequalities that are active or violated at $x$. This mission uses $\Omega(x,0)$ only.
--
--   These objects are shared by SAKKT, AGP(0), SAKKT-regularity and every theorem of the mission. The polar cone, the outer limit (1.6), the normal cone and the projection predicate are not in this file: they come from the shared module `StrictCQ.AGP.Setting`, which this file imports.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)` and the paper's 1-based indices are `Fin m`, `Fin p`. Gradients are Mathlib's `gradient`; the standing $\mathrm C^1$ hypothesis is a separate predicate that theorems assume. $\gamma$ is an extended real (`EReal`), used only in the order comparison $\gamma<g_j(x)$, never in arithmetic.
-- source:
--   Andreani, Martínez, Ramos & Silva, Strict constraint qualifications and sequential optimality conditions for constrained optimization, Optimization Online 5197 (version of November 12, 2015), pp. 1–6, (1.1), (3.7), (4.2)

import Mathlib
import Definitions.Def_StrictCQ_AGP_Setting

open Filter Topology InnerProductSpace

namespace StrictCQ.SAKKT

/-- The constraint data of problem (1.1): equality constraints `h i` (`i : Fin m`, the paper's
`i ∈ {1, …, m}`) and inequality constraints `g j` (`j : Fin p`) on `ℝⁿ = EuclideanSpace ℝ (Fin n)`. -/
structure Constraints (n m p : ℕ) where
  h : Fin m → EuclideanSpace ℝ (Fin n) → ℝ
  g : Fin p → EuclideanSpace ℝ (Fin n) → ℝ

variable {n m p : ℕ}

/-- Standing hypothesis of the paper: every constraint function is continuously differentiable. -/
def Constraints.IsC1 (C : Constraints n m p) : Prop :=
  (∀ i, ContDiff ℝ 1 (C.h i)) ∧ ∀ j, ContDiff ℝ 1 (C.g j)

/-- The feasible set `Ω = {x | h(x) = 0, g(x) ≤ 0}`. -/
def Constraints.feasible (C : Constraints n m p) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | (∀ i, C.h i x = 0) ∧ ∀ j, C.g j x ≤ 0}

/-- KKT at `xs` for the objective `f` (multiplier form): there are `λ ∈ ℝᵐ` and `μ ∈ ℝᵖ₊`, with
`μ j = 0` for every inactive `j`, such that `∇f(xs) + Σ λᵢ ∇hᵢ(xs) + Σ μⱼ ∇gⱼ(xs) = 0`. -/
def Constraints.IsKKT (C : Constraints n m p) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (xs : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ (lam : Fin m → ℝ) (mu : Fin p → ℝ), (∀ j, 0 ≤ mu j) ∧ (∀ j, C.g j xs ≠ 0 → mu j = 0) ∧
    gradient f xs + ∑ i, lam i • gradient (C.h i) xs + ∑ j, mu j • gradient (C.g j) xs = 0

/-- The linearized cone (3.7) `L_Ω(xs)`. -/
def Constraints.linCone (C : Constraints n m p) (xs : EuclideanSpace ℝ (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {d | (∀ i, ⟪gradient (C.h i) xs, d⟫_ℝ = 0) ∧
    ∀ j, C.g j xs = 0 → ⟪gradient (C.g j) xs, d⟫_ℝ ≤ 0}

/-- The linearized set `Ω(x, γ)` of (4.2), with `γ ∈ [-∞, 0]` an extended real (`γ = ⊥` is `-∞`).
At `γ = 0` the third family of rows is vacuous. -/
def Constraints.linSet (C : Constraints n m p) (x : EuclideanSpace ℝ (Fin n)) (γ : EReal) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {z | (∀ i, ⟪gradient (C.h i) x, z - x⟫_ℝ = 0) ∧
    (∀ j, 0 ≤ C.g j x → ⟪gradient (C.g j) x, z - x⟫_ℝ ≤ 0) ∧
    (∀ j, γ < (C.g j x : EReal) → C.g j x < 0 →
      C.g j x + ⟪gradient (C.g j) x, z - x⟫_ℝ ≤ 0)}

end StrictCQ.SAKKT


