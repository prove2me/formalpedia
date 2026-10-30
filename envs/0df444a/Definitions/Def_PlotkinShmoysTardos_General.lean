-- Prove2me | Definitions.Def_PlotkinShmoysTardos_General
-- name    : PlotkinShmoysTardos_General
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:50:30.686205+00:00
-- url     : https://prove2.me/theorems/58fc38c4-bd2d-4419-83b2-8673ea31be17
-- title:
--   The GENERAL problem: width bound, minimization subroutine (10), approximate and exact solutions
-- statement:
--   The **GENERAL problem** asks, for an arbitrary real $m\times n$ matrix $A$ with rows $a_1,\dots,a_m$, an arbitrary vector $b\in\mathbb R^m$ and a convex set $P\subseteq\mathbb R^n$, whether some $x\in P$ satisfies $Ax\le b$. A positive vector $d\in\mathbb R^m$ measures the error. This definition fixes four notions.
--
--   1. **Width bound.** A number $\rho$ is a width bound for $P$ relative to $Ax\le b$ and $d$ if
--   $$
--   |a_i x-b_i|\le \rho\, d_i\qquad\text{for all } i \text{ and all } x\in P .
--   $$
--   The paper's width $\rho=\max_i\max_{x\in P}|a_ix-b_i|/d_i$ is the least such number.
--   2. **Minimization subroutine (10).** A map $O:\mathbb R^m\to\mathbb R^n$ is a subroutine (10) for $P$ and $A$ if for every $y\ge 0$ the point $\tilde x=O(y)$ lies in $P$ and minimizes the cost $c\,x$ over $P$, where $c=y^tA$:
--   $$
--   c\,\tilde x=\min(c\,x : x\in P).
--   $$
--   3. **$\varepsilon$-approximate solution:** a point $x\in P$ with $Ax\le b+\varepsilon d$.
--   4. **Exact solution:** a point $x\in P$ with $Ax\le b$.
--
--   These are the objects of §4 of the paper: the algorithm accesses $P$ only through the subroutine, and its running time is measured in calls to it, as a function of the width.
--
--   **Formalization Note** Vectors are functions `Fin m → ℝ`, `Fin n → ℝ`; row $i$ of $Ax$ is `A.mulVec x i` and $y^tA$ is `Matrix.vecMul y A`. The width is a hypothesis on a number $\rho$ rather than a supremum, so no attainment is assumed.
-- source:
--   Plotkin, Shmoys, Tardos, Fast Approximation Algorithms for Fractional Packing and Covering Problems, Cornell ORIE Technical Report No. 999 (Feb. 1992), §4, p. 23 (GENERAL; subroutine (10); ε-approximate and exact solutions; width ρ)

import Mathlib

namespace PlotkinShmoysTardos

/-! # The GENERAL problem (Plotkin–Shmoys–Tardos, Cornell ORIE TR 999, 1992, §4, p. 23)

GENERAL: does some `x ∈ P` satisfy `A x ≤ b`, where `A` is an arbitrary real `m × n` matrix,
`b` an arbitrary vector and `P ⊆ ℝⁿ` a convex set. Row `i` of `A x` is `A.mulVec x i`;
the error vector `d` is positive. -/

/-- **Width bound.** §4, p. 23: the width of `P` relative to `A x ≤ b` and `d` is
`ρ = maxᵢ max_{x ∈ P} |aᵢ x − bᵢ| / dᵢ`. `IsWidthBound A b d P ρ` says that `ρ` bounds every
ratio `|aᵢ x − bᵢ| / dᵢ` on `P` (written without division: `|aᵢ x − bᵢ| ≤ ρ dᵢ`). -/
def IsWidthBound {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    (P : Set (Fin n → ℝ)) (ρ : ℝ) : Prop :=
  ∀ i, ∀ x ∈ P, |A.mulVec x i - b i| ≤ ρ * d i

/-- **The minimization subroutine (10).** §4, p. 23: "Given an m-dimensional vector `y ≥ 0`,
find a point `x̃ ∈ P` such that `c x̃ = min(c x : x ∈ P)` where `c = yᵗA`."
`IsMinOracle A P O` says that the map `O` is such a subroutine: for every `y ≥ 0`, `O y ∈ P`
and `O y` minimizes `x ↦ (yᵗA) x` over `P`. -/
def IsMinOracle {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (P : Set (Fin n → ℝ))
    (O : (Fin m → ℝ) → (Fin n → ℝ)) : Prop :=
  ∀ y : Fin m → ℝ, 0 ≤ y →
    O y ∈ P ∧ ∀ x ∈ P, Matrix.vecMul y A ⬝ᵥ O y ≤ Matrix.vecMul y A ⬝ᵥ x

/-- **ε-approximate solution.** §4, p. 23: a point `x ∈ P` with `A x ≤ b + ε d`. -/
def IsApprox {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    (P : Set (Fin n → ℝ)) (ε : ℝ) (x : Fin n → ℝ) : Prop :=
  x ∈ P ∧ ∀ i, A.mulVec x i ≤ b i + ε * d i

/-- **Exact solution.** §4, p. 23: a point `x ∈ P` with `A x ≤ b`. -/
def IsExact {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (P : Set (Fin n → ℝ)) (x : Fin n → ℝ) : Prop :=
  x ∈ P ∧ ∀ i, A.mulVec x i ≤ b i

end PlotkinShmoysTardos


