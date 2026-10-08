-- Prove2me | Definitions.Def_ExecCompLP_Consistency_Setting
-- name    : ExecCompLP_Consistency_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T05:11:23.31281+00:00
-- url     : https://prove2.me/theorems/3c9d1f54-f818-4646-bb3f-cc8c425e406d
-- title:
--   §8, pp. 149–150 — the LP (8), its feasible set and minimisers, assumptions (I), (II), and nondegeneracy
-- statement:
--   This file fixes the objects of the Appendix (§8) of Charnes, Cooper and Ferguson (1955). Throughout, $m$ is the number of constraints (rows, indexed by $i$) and $n$ the number of variables (columns, indexed by $j$). For a real $m\times n$ matrix $X=(x_{ij})$, a right-hand side $b\in\mathbb R^m$ and a cost vector $c\in\mathbb R^n$, the linear program (8) is
--
--   $$\min \sum_j c_j a_j \quad\text{subject to}\quad \sum_j x_{ij} a_j \ge b_i\ (i=1,\dots,m),\qquad a_j\ge 0\ (j=1,\dots,n).$$
--
--   1. The **feasible set** $F(X,b)$ is the set of $a\in\mathbb R^n$ with $a_j\ge 0$ for every $j$ and $\sum_j x_{ij}a_j\ge b_i$ for every $i$.
--   2. A vector $a$ is a **minimizing solution** of (8) if $a\in F(X,b)$ and $\sum_j c_j a_j\le\sum_j c_j a'_j$ for every $a'\in F(X,b)$.
--   3. **Assumption (I)** for the true matrix $\xi=(\xi_{ij})$ and a vector $\hat\alpha$: the program (8) with $\xi$ in place of $X$ has a unique solution vector $\hat\alpha$, i.e. $\hat\alpha$ is a minimizing solution and every minimizing solution equals $\hat\alpha$.
--   4. **Assumption (II)**: every set of $m$ columns of $\xi$ is linearly independent in $\mathbb R^m$ (vacuous when $n<m$).
--   5. The **positive support** of a point $a$ is a subset of the index set $\{1,\dots,n\}\sqcup\{1,\dots,m\}$: it contains the variable $j$ when $a_j>0$, and the constraint $i$ when its surplus $s_i=\sum_j x_{ij}a_j-b_i$ is strictly positive.
--   6. The **augmented columns** are the columns of the matrix $[X,\,-I_m]$ obtained by adding one surplus variable per constraint: column $j$ of $X$ for the variable $j$, and $-e_i$ for the surplus variable of constraint $i$.
--   7. A point $a$ is **nondegenerate** if the number of strictly positive variables $a_j$ plus the number of constraints with strictly positive surplus equals exactly $m$.
--
--   These are the objects the consistency theorem of §8 and the steps of its proof speak about.
--
--   **Formalization Note** Matrices are `Matrix (Fin m) (Fin n) ℝ` with `X i j` the entry $x_{ij}$, so `fun i => X i j` is column $j$; indices are 0-based. No optimal value is defined (no `sInf`): minimality is stated pointwise. The nondegeneracy predicate is not in the paper; it is the one hypothesis the series adds to the consistency claim (see the goal theorem), and it is used only at the true optimum $\hat\alpha$.
-- source:
--   Charnes, Cooper & Ferguson, Optimal estimation of executive compensation by linear programming, Management Science 1(2) (1955), pp. 149–150, §8, (8), (I), (II)

import Mathlib

namespace ExecCompLP.Consistency

/-- The feasible set of the linear program (8) (§8, p. 149) for the coefficient matrix `X`
(rows `i : Fin m` are the constraints, columns `j : Fin n` the variables) and right-hand side `b`:
the vectors `a` with `a j ≥ 0` for all `j` and `∑ j, X i j * a j ≥ b i` for all `i`. -/
def feasibleSet {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) : Set (Fin n → ℝ) :=
  {a | (∀ j, 0 ≤ a j) ∧ ∀ i, b i ≤ ∑ j, X i j * a j}

/-- `a` is a minimizing solution of (8): it is feasible and no feasible point has a smaller value
of `∑ j, c j * a j`. -/
def IsMinimizer {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (a : Fin n → ℝ) : Prop :=
  a ∈ feasibleSet X b ∧ ∀ a' ∈ feasibleSet X b, ∑ j, c j * a j ≤ ∑ j, c j * a' j

/-- Assumption (I) of §8 (p. 150): the true program (with matrix `ξ`) has a unique solution
vector `αhat` (it is a minimizer, and every minimizer equals it). -/
def AssumptionI {m n : ℕ} (ξ : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (αhat : Fin n → ℝ) : Prop :=
  IsMinimizer ξ b c αhat ∧ ∀ a, IsMinimizer ξ b c a → a = αhat

/-- Assumption (II) of §8 (p. 150): every `m`-column subset of `ξ` is linearly independent
(`m` is the number of rows). -/
def AssumptionII {m n : ℕ} (ξ : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ S : Finset (Fin n), S.card = m → LinearIndependent ℝ (fun j : S => fun i => ξ i j)

/-- The positive part of the augmented solution `(a, s)`, `s = X a - b` the surplus vector:
`Sum.inl j` if `a j > 0`, and `Sum.inr i` if the `i`-th constraint has positive surplus. -/
def posSupp {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (a : Fin n → ℝ) :
    Fin n ⊕ Fin m → Prop
  | Sum.inl j => 0 < a j
  | Sum.inr i => b i < ∑ j, X i j * a j

/-- The columns of the augmented matrix `[X, -I]`: column `j` of `X` for a variable `j`, and
`-eᵢ` for the surplus variable of constraint `i`. -/
def augCol {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℝ) : Fin n ⊕ Fin m → (Fin m → ℝ)
  | Sum.inl j => fun i => X i j
  | Sum.inr i' => fun i => if i = i' then -1 else 0

/-- Nondegeneracy of `a` (an addition to the paper, disclosed): the number of strictly positive
variables plus the number of constraints with strictly positive surplus is exactly `m`. -/
def Nondegenerate {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (a : Fin n → ℝ) :
    Prop :=
  (Finset.univ.filter (fun j => 0 < a j)).card
    + (Finset.univ.filter (fun i => b i < ∑ j, X i j * a j)).card = m

end ExecCompLP.Consistency


