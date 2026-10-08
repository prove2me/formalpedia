-- Prove2me | Definitions.Def_MatousekLP_InteriorPoint_CentralPath
-- name    : MatousekLP_InteriorPoint_CentralPath
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T11:29:14.468265+00:00
-- url     : https://prove2.me/theorems/e6f19beb-f0ef-4935-b473-dc1d848ad00d
-- title:
--   §7.2 — the equational-form LP (7.2), its dual (7.5), the barrier $f_\mu$ and the central-path system (7.4)
-- statement:
--   This module fixes the objects of the first half of §7.2 of Matoušek & Gärtner. Let $A$ be a real $m\times n$ matrix, $b\in\mathbb{R}^m$ and $c\in\mathbb{R}^n$, and consider the linear program in equational form (7.2) and its dual (7.5):
--
--   $$\text{(7.2)}\ \ \text{maximize } c^{T}x \ \text{ s.t. } Ax=b,\ x\ge 0, \qquad \text{(7.5)}\ \ \text{minimize } b^{T}y \ \text{ s.t. } A^{T}y\ge c,\ y\in\mathbb{R}^m .$$
--
--   1. A **feasible solution** of (7.2) is an $x$ with $Ax=b$ and $x\ge 0$; it is an **interior** feasible solution if moreover $x>0$, meaning that every coordinate of $x$ is strictly positive.
--   2. A vector $y\in\mathbb{R}^m$ is an **interior** feasible solution of (7.5) if its slack vector $s=A^{T}y-c$ satisfies $s>0$ (this implies $A^{T}y\ge c$).
--   3. For $\mu\in\mathbb{R}$ the **barrier function** is
--   $$f_\mu(x)=c^{T}x+\mu\sum_{j=1}^{n}\ln x_j ,$$
--   considered only for $x>0$.
--   4. A vector $x$ is the **unique maximizer of $f_\mu$ subject to $Ax=b$, $x>0$** if $Ax=b$, $x>0$, and $f_\mu(x')<f_\mu(x)$ for every other $x'\ne x$ with $Ax'=b$, $x'>0$.
--   5. The **central-path system** (7.4) with unknowns $x,s\in\mathbb{R}^n$, $y\in\mathbb{R}^m$ is
--   $$Ax=b,\qquad A^{T}y-s=c,\qquad (s_1x_1,\dots,s_nx_n)=\mu\mathbf 1,\qquad x,s\ge 0 .$$
--
--   Solutions of (7.4) for $\mu>0$ form the primal–dual central path, which interior point methods follow towards an optimum of (7.2).
--
--   **Formalization Note** Vectors are functions `Fin n → ℝ`, so the book's indices $1,\dots,n$ become $0,\dots,n-1$. Lean's `Real.log` returns $0$ at nonpositive arguments; the barrier is therefore only ever compared on points with all coordinates strictly positive. The rank assumption on $A$ from (7.2) is a hypothesis of each theorem, not part of these definitions.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, §7.2, p. 119 (eq. (7.2), barrier f_μ, auxiliary problem), p. 120 (system (7.4), eq. (7.5)), p. 121 (Lemma 7.2.1 hypotheses)

import Mathlib

namespace MatousekLP.InteriorPoint

/-!
# The primal–dual central path of a linear program in equational form

Matoušek & Gärtner, *Understanding and Using Linear Programming*, Springer 2007, §7.2,
pp. 119–121: the linear program (7.2) `maximize cᵀx subject to Ax = b, x ≥ 0`, its dual (7.5)
`minimize bᵀy subject to Aᵀy ≥ c`, the barrier function `f_μ(x) = cᵀx + μ · Σⱼ ln xⱼ`, and the
system (7.4) whose solutions form the central path.

`A : Matrix (Fin m) (Fin n) ℝ`, `b : Fin m → ℝ`, `c : Fin n → ℝ`. The book's indices
`1, …, n` are `0, …, n-1` here.
-/

open Matrix

variable {m n : ℕ}

/-- `x` is a feasible solution of (7.2): `Ax = b` and `x ≥ 0` (p. 119). -/
def IsPrimalFeasible (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) : Prop :=
  A *ᵥ x = b ∧ 0 ≤ x

/-- `x` is a feasible solution of (7.2) with `x > 0`, i.e. all coordinates strictly positive
(p. 119). -/
def IsPrimalInterior (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) : Prop :=
  A *ᵥ x = b ∧ ∀ j, 0 < x j

/-- `y` is a feasible solution of the dual (7.5), `Aᵀy ≥ c`, whose slack vector
`s = Aᵀy − c` satisfies `s > 0` (p. 121, hypothesis of Lemma 7.2.1). -/
def IsDualInterior (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (y : Fin m → ℝ) : Prop :=
  ∀ j, 0 < (Aᵀ *ᵥ y - c) j

/-- The barrier function `f_μ(x) = cᵀx + μ · Σ_{j=1}^n ln xⱼ` (p. 119). It is only meaningful
for `x > 0`; every statement using it restricts to such `x`. -/
noncomputable def barrier (c : Fin n → ℝ) (μ : ℝ) (x : Fin n → ℝ) : ℝ :=
  c ⬝ᵥ x + μ * ∑ j, Real.log (x j)

/-- `x` is the unique maximizer of `f_μ` subject to `Ax = b` and `x > 0`: it satisfies the
constraints, and `f_μ(x') < f_μ(x)` for every other `x'` satisfying them (p. 121). -/
def IsUniqueBarrierMaximizer (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (μ : ℝ) (x : Fin n → ℝ) : Prop :=
  IsPrimalInterior A b x ∧
    ∀ x', IsPrimalInterior A b x' → x' ≠ x → barrier c μ x' < barrier c μ x

/-- The system (7.4) with unknowns `x, s ∈ ℝⁿ`, `y ∈ ℝᵐ` (p. 120):
`Ax = b`, `Aᵀy − s = c`, `(s₁x₁, …, sₙxₙ) = μ𝟏`, `x, s ≥ 0`. -/
def CentralPathSystem (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (μ : ℝ) (x : Fin n → ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ) : Prop :=
  A *ᵥ x = b ∧ Aᵀ *ᵥ y - s = c ∧ (∀ j, s j * x j = μ) ∧ 0 ≤ x ∧ 0 ≤ s

end MatousekLP.InteriorPoint


