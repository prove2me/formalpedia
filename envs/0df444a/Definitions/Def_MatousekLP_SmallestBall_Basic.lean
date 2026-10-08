-- Prove2me | Definitions.Def_MatousekLP_SmallestBall_Basic
-- name    : MatousekLP_SmallestBall_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T21:32:37.200568+00:00
-- url     : https://prove2.me/theorems/3abb1cb1-e81b-4f76-9303-2b7d46731f4a
-- title:
--   Convex programs in equational form, program (8.15), and the unique smallest enclosing ball
-- statement:
--   Section 8.7 of Matoušek & Gärtner studies convex programs and the smallest ball enclosing a finite point set. This module fixes the vocabulary.
--
--   1. **Convex program in equational form** (8.11). For a real $m\times n$ matrix $A$, a vector $b\in\mathbb{R}^m$ and a function $f:\mathbb{R}^n\to\mathbb{R}$, the problem is
--   $$\text{minimize } f(x)\ \text{ subject to } Ax=b,\ x\ge 0 .$$
--   A vector $x\in\mathbb{R}^n$ is **feasible** if $Ax=b$ and $x_j\ge 0$ for all $j$, and **optimal** if it is feasible and $f(x)\le f(x')$ for every feasible $x'$.
--   2. **The point matrix.** For points $p_1,\dots,p_n\in\mathbb{R}^d$, $Q$ is the $d\times n$ matrix whose $j$th column consists of the $d$ coordinates of $p_j$.
--   3. **Program (8.15).** Its objective is
--   $$f(x)=x^{T}Q^{T}Qx-\sum_{j=1}^{n}x_j\,p_j^{T}p_j ,$$
--   and its constraints are $\sum_{j=1}^n x_j=1$ and $x\ge 0$. Feasible and optimal solutions are defined as in item 1.
--   4. **Unique smallest enclosing ball.** Balls in $\mathbb{R}^d$ are closed Euclidean balls $B(c,r)=\{z:\|z-c\|\le r\}$. The ball $B(c,r)$ is the **unique smallest enclosing ball** of a set $S\subseteq\mathbb{R}^d$ if $r\ge 0$, $S\subseteq B(c,r)$, every ball $B(c',r')$ containing $S$ satisfies $r\le r'$, and every ball $B(c',r')$ containing $S$ with $r'\le r$ has $c'=c$.
--
--   These notions are the language of Proposition 8.7.2, Lemma 8.7.3 and Theorem 8.7.4.
--
--   **Formalization Note** Vectors in $\mathbb{R}^n$ are functions `Fin n → ℝ`, so the book's indices $1,\dots,n$ are $0,\dots,n-1$; points of $\mathbb{R}^d$ live in `EuclideanSpace ℝ (Fin d)`, so distances and $p^Tq$ are Euclidean. Optimality is stated against every feasible point; no infimum is taken. A ball is identified by its center and radius; competitors with negative radius (empty balls) are allowed in the definition but never contain a nonempty set.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, §8.7: p. 184 (smallest ball problem), p. 186 (convex program in equational form (8.11)), p. 188 (smallest enclosing ball, Lemma 8.7.3), p. 190 (matrix Q and program (8.15), Theorem 8.7.4)

import Mathlib
import Definitions.Def_MatousekLP_BFS_EquationalForm

namespace MatousekLP.SmallestBall

/-!
# Convex programs in equational form and smallest enclosing balls (§8.7)

Matoušek & Gärtner, *Understanding and Using Linear Programming*, Springer 2007, §8.7,
pp. 184–191.

* A convex program in equational form (8.11), p. 186: minimize `f(x)` subject to `Ax = b`,
  `x ≥ 0`, where `A ∈ ℝ^{m×n}`, `b ∈ ℝ^m`.  Feasible and optimal solutions are defined against
  every feasible point (no infimum is taken).
* For points `p₁, …, pₙ ∈ ℝ^d`, the `d × n` matrix `Q` whose `j`th column is `pⱼ`, and the
  objective `f(x) = xᵀQᵀQx − ∑ⱼ xⱼ pⱼᵀpⱼ` of program (8.15), p. 190, whose feasible set is
  `∑ⱼ xⱼ = 1`, `x ≥ 0`.
* Balls in `ℝ^d` are closed Euclidean balls `{x : ‖x − c‖ ≤ r}`.  `B(c, r)` is *the unique
  smallest enclosing ball* of a set `S` if it contains `S`, every closed ball containing `S` has
  radius at least `r`, and every closed ball containing `S` with radius at most `r` has center `c`.

Indices are 0-based (`Fin n`): the book's `x₁, x₂, …` are `x 0, x 1, …`.
-/

open Matrix
open scoped RealInnerProductSpace

/-- `x` is an optimal solution of "minimize `f(x)` subject to `Ax = b`, `x ≥ 0`": it is feasible
and `f x ≤ f x'` for every feasible `x'`. -/
def IsOptimal {m n : ℕ} (f : (Fin n → ℝ) → ℝ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x : Fin n → ℝ) : Prop :=
  MatousekLP.BFS.IsFeasible A b x ∧ ∀ x' : Fin n → ℝ, MatousekLP.BFS.IsFeasible A b x' → f x ≤ f x'

/-- The `d × n` matrix `Q` whose `j`th column is formed by the `d` coordinates of `pⱼ`. -/
def pointMatrix {d n : ℕ} (p : Fin n → EuclideanSpace ℝ (Fin d)) : Matrix (Fin d) (Fin n) ℝ :=
  Matrix.of fun i j => p j i

/-- The objective of (8.15): `f(x) = xᵀ QᵀQ x − ∑ⱼ xⱼ pⱼᵀpⱼ`. -/
noncomputable def ballObjective {d n : ℕ} (p : Fin n → EuclideanSpace ℝ (Fin d)) (x : Fin n → ℝ) : ℝ :=
  x ⬝ᵥ (((pointMatrix p)ᵀ * pointMatrix p) *ᵥ x) - ∑ j, x j * ⟪p j, p j⟫

/-- Feasibility for (8.15): `∑ⱼ xⱼ = 1` and `x ≥ 0`. -/
def IsFeasibleBallQP {n : ℕ} (x : Fin n → ℝ) : Prop :=
  ∑ j, x j = 1 ∧ 0 ≤ x

/-- `x` is an optimal solution of (8.15): feasible, and `f x ≤ f x'` for every feasible `x'`. -/
def IsOptimalBallQP {d n : ℕ} (p : Fin n → EuclideanSpace ℝ (Fin d)) (x : Fin n → ℝ) : Prop :=
  IsFeasibleBallQP x ∧ ∀ x' : Fin n → ℝ, IsFeasibleBallQP x' → ballObjective p x ≤ ballObjective p x'

/-- The closed ball with center `c` and radius `r` is the unique smallest enclosing ball of `S`:
`0 ≤ r`, it contains `S`, every closed ball `B(c', r')` containing `S` has `r ≤ r'`, and if moreover
`r' ≤ r` then `c' = c`. -/
def IsUniqueSmallestEnclosingBall {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d)))
    (c : EuclideanSpace ℝ (Fin d)) (r : ℝ) : Prop :=
  0 ≤ r ∧ S ⊆ Metric.closedBall c r ∧
    ∀ (c' : EuclideanSpace ℝ (Fin d)) (r' : ℝ), S ⊆ Metric.closedBall c' r' →
      r ≤ r' ∧ (r' ≤ r → c' = c)

end MatousekLP.SmallestBall


