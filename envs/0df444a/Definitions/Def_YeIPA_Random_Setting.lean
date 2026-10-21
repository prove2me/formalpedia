-- Prove2me | Definitions.Def_YeIPA_Random_Setting
-- name    : YeIPA_Random_Setting
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:57:29.417627+00:00
-- url     : https://prove2.me/theorems/c248282e-4318-4de3-9608-3050f52bb443
-- title:
--   Systems (6.5), (6.11), (6.12), the standard Gaussian matrix model, $p_{nd}$, and the uniform law on the unit sphere
-- statement:
--   Fix integers $m,n\ge0$ and a real $m\times n$ matrix $A$ with columns $a_1,\dots,a_n$. Vector inequalities are componentwise. This module defines the objects of Chapter 6 (Average-Case Analysis) of Ye's *Interior Point Algorithms*.
--
--   1. **System (6.5)** (p. 187), the homogeneous feasibility problem
--   $$\mathcal X=\{x\in\mathbb R^n:\ Ax=0,\ x\ge0,\ x\ne0\}.$$
--   A **feasible point** is an element of $\mathcal X$; an **interior feasible point** is a feasible point with $x>0$ (every coordinate strictly positive).
--   2. **System (6.11)** (p. 194), its alternative: $s=A^Ty\ge0$, $s\ne0$, for some $y\in\mathbb R^m$. A feasible point is such a $y$; an interior feasible point is a feasible $y$ with $s=A^Ty>0$.
--   3. **System (6.12)** (p. 194). A partition $A=(A_B,A_N)$ chooses $m$ distinct columns, in an order, through an injection $\sigma:\{1,\dots,m\}\to\{1,\dots,n\}$: $A_B=(a_{\sigma(1)},\dots,a_{\sigma(m)})$ is $m\times m$ and $A_N$ consists of the remaining $n-m$ columns, so that $A_Ne=\sum_{j\notin\sigma(\{1,\dots,m\})}a_j$ ($e$ the all-ones vector; $A_Ne=0$ when no column remains). A vector $x=(x_B,x_{m+1})\in\mathbb R^{m+1}$, with $x_B\in\mathbb R^m$, is feasible for (6.12) if
--   $$A_Bx_B+(A_Ne)\,x_{m+1}=0,\qquad x\ne0,\qquad x\ge0.$$
--   4. **The standard Gaussian model** (§6.2.2, p. 193): the probability measure on $m\times n$ real matrices under which the $mn$ entries are independent standard Gaussian $N(0,1)$ variables.
--   5. **The number $p_{nd}$** of Corollaries 6.11–6.12 (p. 193), for $n\ge1$ and $d\ge0$:
--   $$p_{nd}=\frac{\binom{n-1}{0}+\binom{n-1}{1}+\cdots+\binom{n-1}{d-1}}{2^{n-1}},$$
--   which is $0$ when $d=0$ (empty sum).
--   6. **The uniform distribution on the unit sphere** $\{v\in\mathbb R^k:\ \|v\|=1\}$ (used in Lemma 6.5, p. 185): the surface measure induced by Lebesgue measure on $\mathbb R^k$, normalized to total mass one ($\|\cdot\|$ the Euclidean norm).
--
--   These are the objects in terms of which the chapter's probabilistic results are stated: the probability that a random homogeneous system is feasible or strictly feasible, the alternative (6.11), and the reduction (6.12) to $m+1$ variables.
--
--   **Formalization Note** Vectors are functions on `Fin n`, so indices $1,\dots,n$ become $0,\dots,n-1$ and $x_{m+1}$ is the last coordinate `x m` of a vector on `Fin (m+1)`. The Gaussian model is the product measure `Measure.pi` (over rows, then columns) of `gaussianReal 0 1` on arrays `Fin m → Fin n → ℝ`, read as the matrix `Matrix.of A`. $p_{nd}$ uses the natural-number $n-1$, so it is only meaningful for $n\ge1$, which every theorem assumes. The sphere law is Mathlib's `volume.toSphere` scaled by the inverse of its total mass; for $k\ge1$ it is a probability measure (for $k=0$ the sphere is empty and the measure is zero). An interior feasible point is required to be feasible as well as strictly positive, which only matters for $n=0$.
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, p. 187 ((6.5)), p. 193 (§6.2.2, Corollaries 6.11–6.12, p_nd), p. 194 ((6.11), Lemma 6.14 (6.12)), p. 185 (Lemma 6.5, uniform distribution on the unit sphere)

import Mathlib

open Matrix MeasureTheory ProbabilityTheory

namespace YeIPA.Random

/-!
# Random homogeneous feasibility problems: systems (6.5), (6.11), (6.12), the Gaussian model,
the probability `p_nd`, and the uniform law on the unit sphere

Ye, *Interior Point Algorithms: Theory and Analysis*, Wiley 1997, Chapter 6: the homogeneous
system (6.5) `X = {x : Ax = 0, x ≥ 0, x ≠ 0}` (p. 187); its alternative (6.11)
`s = Aᵀy ≥ 0, s ≠ 0` (p. 194); system (6.12) of Lemma 6.14 for a partition `A = (A_B, A_N)`
(p. 194); the standard Gaussian model of §6.2.2 and the number `p_nd` of Corollaries 6.11–6.12
(p. 193); the uniform distribution on the unit sphere used in Lemma 6.5 (p. 185).

`A : Matrix (Fin m) (Fin n) ℝ`. The book's indices `1, …, n` are `0, …, n-1` here. Vector
inequalities are componentwise. An *interior feasible point* is a feasible point all of whose
coordinates (of `x`, resp. of `s = Aᵀy`) are strictly positive.
-/

variable {m n : ℕ}

/-- `x` is a feasible point of system (6.5): `Ax = 0`, `x ≥ 0`, `x ≠ 0`. -/
def IsFeasible65 (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) : Prop :=
  A *ᵥ x = 0 ∧ (∀ j, 0 ≤ x j) ∧ x ≠ 0

/-- `x` is an interior feasible point of system (6.5): feasible and `x > 0`. -/
def IsInterior65 (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) : Prop :=
  IsFeasible65 A x ∧ ∀ j, 0 < x j

/-- `y` gives a feasible point of system (6.11): `s = Aᵀy` satisfies `s ≥ 0`, `s ≠ 0`. -/
def IsFeasible611 (A : Matrix (Fin m) (Fin n) ℝ) (y : Fin m → ℝ) : Prop :=
  (∀ j, 0 ≤ (Aᵀ *ᵥ y) j) ∧ Aᵀ *ᵥ y ≠ 0

/-- `y` gives an interior feasible point of system (6.11): feasible and `s = Aᵀy > 0`. -/
def IsInterior611 (A : Matrix (Fin m) (Fin n) ℝ) (y : Fin m → ℝ) : Prop :=
  IsFeasible611 A y ∧ ∀ j, 0 < (Aᵀ *ᵥ y) j

/-- The column sum `A_N e = Σ_{j ∈ N} a_j` over the columns `N` of `A` that are not chosen by
`σ`. -/
def colSumN (A : Matrix (Fin m) (Fin n) ℝ) (σ : Fin m ↪ Fin n) : Fin m → ℝ :=
  fun i => ∑ j ∈ (Finset.univ.map σ)ᶜ, A i j

/-- System (6.12) for the partition `A = (A_B, A_N)` in which `A_B` is the `m × m` matrix of the
columns `σ 0, …, σ (m-1)` and `A_N` the matrix of the remaining `n − m` columns: the vector
`x ∈ ℝ^{m+1}`, written `x = (x_B, x_{m+1})` with `x_B = (x 0, …, x (m-1))` and
`x_{m+1} = x m`, satisfies `A_B x_B + (A_N e) x_{m+1} = 0`, `x ≠ 0` and `x ≥ 0`. -/
def IsFeasible612 (A : Matrix (Fin m) (Fin n) ℝ) (σ : Fin m ↪ Fin n) (x : Fin (m + 1) → ℝ) :
    Prop :=
  (A.submatrix id σ) *ᵥ (fun k : Fin m => x (Fin.castSucc k)) + x (Fin.last m) • colSumN A σ = 0
    ∧ x ≠ 0 ∧ ∀ k, 0 ≤ x k

/-- The standard Gaussian model of §6.2.2: the law on `m × n` real arrays under which every
entry is an independent standard Gaussian `N(0, 1)` variable. A sample `A` is read as the matrix
`Matrix.of A`. -/
noncomputable def gaussianMatrix (m n : ℕ) : Measure (Fin m → Fin n → ℝ) :=
  Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n => gaussianReal 0 1

/-- The number `p_nd = (C(n−1, 0) + ⋯ + C(n−1, d−1)) / 2^{n−1}` of Corollaries 6.11–6.12
(an empty sum when `d = 0`). -/
noncomputable def pnd (n d : ℕ) : ℝ :=
  (∑ i ∈ Finset.range d, ((n - 1).choose i : ℝ)) / 2 ^ (n - 1)

/-- The uniform probability distribution on the unit sphere `{v : ‖v‖ = 1}` of the Euclidean
space `ℝ^k`: the surface measure induced by Lebesgue measure, normalized to total mass one. -/
noncomputable def uniformSphere (k : ℕ) :
    Measure (Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1) :=
  ((volume : Measure (EuclideanSpace ℝ (Fin k))).toSphere Set.univ)⁻¹ •
    (volume : Measure (EuclideanSpace ℝ (Fin k))).toSphere

end YeIPA.Random


