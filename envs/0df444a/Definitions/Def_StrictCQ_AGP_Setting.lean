-- Prove2me | Definitions.Def_StrictCQ_AGP_Setting
-- name    : StrictCQ_AGP_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T22:36:47.488424+00:00
-- url     : https://prove2.me/theorems/57443c96-9919-4f66-a1c6-4c15e3fe360e
-- title:
--   (1.1), (1.6), (3.7), (4.2), pp. 1–6 — constraint system, KKT, linearized cone, polar, outer limit, normal cone, projection, Ω(x, γ)
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
--   3. **Linearized cone (3.7)** $L_\Omega(x^*)=\{d : \langle\nabla h_i(x^*),d\rangle=0\ \forall i,\ \langle\nabla g_j(x^*),d\rangle\le0\ \forall j\in J(x^*)\}$, and the **polar** $K^\circ=\{v:\langle v,k\rangle\le 0\ \forall k\in K\}$.
--   4. **Outer limit (1.6).** For a set-valued map $F$, $\limsup_{z\to z^*}F(z)$ is the set of all $w^*$ for which there are $z^k\to z^*$ and $w^k\to w^*$ with $w^k\in F(z^k)$. A version restricted to $z^k$ in a domain $D$ is also provided.
--   5. **Normal cone** of a convex set $S$ at $y$: $N_S(y)=\{w : \langle w,z-y\rangle\le0\ \forall z\in S\}$ if $y\in S$, and $N_S(y)=\emptyset$ if $y\notin S$.
--   6. **Projection.** $y$ is a Euclidean projection of $z$ onto $S$ if $y\in S$ and $\|z-y\|\le\|z-w\|$ for all $w\in S$.
--   7. **The linearized sets (4.2).** For $\gamma\in[-\infty,0]$,
--   $$\Omega(x,\gamma)=\left\{z:\ \begin{array}{ll}\langle\nabla h_i(x),z-x\rangle=0, & \text{for all } i\\ \langle\nabla g_j(x),z-x\rangle\le0, & \text{if } 0\le g_j(x)\\ g_j(x)+\langle\nabla g_j(x),z-x\rangle\le 0, & \text{if } \gamma<g_j(x)<0\end{array}\right\}.$$
--   At $\gamma=0$ the third family of rows is empty; at $\gamma=-\infty$ it covers every $j$ with $g_j(x)<0$.
--
--   These objects are shared by the AGP condition, AGP-regularity and every theorem of the mission.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)` and the paper's 1-based indices are `Fin m`, `Fin p`. Gradients are Mathlib's `gradient`; the standing $\mathrm C^1$ hypothesis is a separate predicate that theorems assume. $\gamma$ is an extended real (`EReal`) and $\gamma=-\infty$ is `⊥`, not a large negative number. The normal cone is empty off the set, as in Rockafellar–Wets, and the projection is a predicate (it exists and is unique on the nonempty closed convex sets used here).
-- source:
--   Andreani, Martínez, Ramos & Silva, Strict constraint qualifications and sequential optimality conditions for constrained optimization, Optimization Online 5197 (version of November 12, 2015), pp. 1–6, (1.1), (1.6), (3.7), (4.2), Proposition 3.1

import Mathlib

open Filter Topology InnerProductSpace

namespace StrictCQ.AGP

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

/-- The polar cone `K° = {v | ⟨v, k⟩ ≤ 0 for all k ∈ K}`. -/
def polar (K : Set (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n)) :=
  {v | ∀ k ∈ K, ⟪v, k⟫_ℝ ≤ 0}

/-- The sequential Painlevé–Kuratowski outer limit (1.6) of `F` at `z₀`, with the arguments
restricted to the domain `D`. -/
def outerLimitWithin {Z W : Type*} [TopologicalSpace Z] [TopologicalSpace W]
    (F : Z → Set W) (D : Set Z) (z₀ : Z) : Set W :=
  {w | ∃ z : ℕ → Z, ∃ v : ℕ → W, (∀ k, z k ∈ D) ∧ Tendsto z atTop (𝓝 z₀) ∧
    Tendsto v atTop (𝓝 w) ∧ ∀ k, v k ∈ F (z k)}

/-- The normal cone of convex analysis, `N_S(y) = {w | ⟨w, z - y⟩ ≤ 0 ∀ z ∈ S}` for `y ∈ S`, and
`N_S(y) = ∅` for `y ∉ S`. -/
def normalCone (S : Set (EuclideanSpace ℝ (Fin n))) (y : EuclideanSpace ℝ (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {w | y ∈ S ∧ ∀ z ∈ S, ⟪w, z - y⟫_ℝ ≤ 0}

/-- `y` is a Euclidean projection of `z` onto `S`: `y ∈ S` and `y` is nearest to `z` in `S`. -/
def IsProj (S : Set (EuclideanSpace ℝ (Fin n))) (z y : EuclideanSpace ℝ (Fin n)) : Prop :=
  y ∈ S ∧ ∀ w ∈ S, ‖z - y‖ ≤ ‖z - w‖

/-- The linearized set `Ω(x, γ)` of (4.2), with `γ ∈ [-∞, 0]` an extended real (`γ = ⊥` is `-∞`).
At `γ = 0` the third family of rows is vacuous. -/
def Constraints.linSet (C : Constraints n m p) (x : EuclideanSpace ℝ (Fin n)) (γ : EReal) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {z | (∀ i, ⟪gradient (C.h i) x, z - x⟫_ℝ = 0) ∧
    (∀ j, 0 ≤ C.g j x → ⟪gradient (C.g j) x, z - x⟫_ℝ ≤ 0) ∧
    (∀ j, γ < (C.g j x : EReal) → C.g j x < 0 →
      C.g j x + ⟪gradient (C.g j) x, z - x⟫_ℝ ≤ 0)}

end StrictCQ.AGP


