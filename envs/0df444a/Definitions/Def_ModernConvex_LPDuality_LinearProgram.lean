-- Prove2me | Definitions.Def_ModernConvex_LPDuality_LinearProgram
-- name    : ModernConvex_LPDuality_LinearProgram
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:31:52.947587+00:00
-- url     : https://prove2.me/theorems/9dc74bb4-2098-43d2-82f9-a927f5542a05
-- title:
--   The LP program $\min\{c^Tx \mid Ax \ge b\}$, its dual $\max\{b^Ty \mid A^Ty = c,\ y \ge 0\}$: feasibility, boundedness, solvability, optimal values
-- statement:
--   Fix finite index sets for the constraints and the variables (in the theorems: $\{1,\dots,m\}$ and $\{1,\dots,n\}$), a constraint matrix $A \in \mathbb R^{m\times n}$ with rows $a_1^T,\dots,a_m^T$, a right-hand side $b \in \mathbb R^m$ and an objective vector $c \in \mathbb R^n$. The **LP program** in Ben-Tal and Nemirovski's standard form is
--   $$\text{(LP)}\qquad \min_x \left\{ c^Tx \;\middle|\; Ax \ge b \right\},$$
--   and its **dual** is
--   $$\text{(LP}^*\text{)}\qquad \max_y \left\{ b^Ty \;\middle|\; A^Ty = c,\ y \ge 0 \right\}.$$
--   All vector inequalities are componentwise. The file defines, following pp. 1–2 and 16–18 of the book:
--
--   1. $x$ is a **feasible solution** of (LP) if $Ax - b \ge 0$; (LP) is **feasible** if it has one.
--   2. (LP) is **bounded below** if there is $L \in \mathbb R$ with $c^Tx \ge L$ for every feasible $x$ (in particular every infeasible program is bounded below, as on p. 1).
--   3. A real $a$ is a **lower bound on the optimal value** $c^*$ of (LP) if $c^Tx \ge a$ for every feasible $x$ (p. 16; every $a$ is one when (LP) is infeasible, where $c^* = +\infty$).
--   4. $x$ is an **optimal solution** of (LP) if it is feasible and $c^Tx \le c^Tx'$ for every feasible $x'$; (LP) is **solvable** if it has an optimal solution.
--   5. $v$ is the **optimal value** of (LP) if $v = \inf\{c^Tx : Ax \ge b\}$ is the greatest lower bound of the set of feasible objective values; no real $v$ has this property when (LP) is infeasible or unbounded below.
--   6. The dual notions: $y$ is **dual feasible** if $A^Ty = c$ and $y \ge 0$; (LP$^*$) is feasible, **bounded above** (some $U$ with $b^Ty \le U$ for all dual feasible $y$), **solvable** (some dual feasible $y$ maximizes $b^Ty$), and $v$ is its optimal value if $v$ is the least upper bound of $\{b^Ty : y \text{ dual feasible}\}$.
--   7. The system (D) of p. 17 in the unknowns $(y, a) \in \mathbb R^m \times \mathbb R$: $y \ge 0$, $A^Ty = \sum_i y_i a_i = c$, $b^Ty \ge a$.
--   8. The rewriting of (LP$^*$) in the form (LP) used in the proof of Theorem 1.3.2 (p. 18): (LP$^*$) is $\min_y\{-b^Ty \mid A'y - b' \ge 0\}$ with
--   $$A' = \begin{bmatrix} I_m \\ A^T \\ -A^T \end{bmatrix}, \qquad b' = \begin{pmatrix} 0 \\ c \\ -c \end{pmatrix},$$
--   whose rows are indexed by the disjoint union of $\{1,\dots,m\}$, $\{1,\dots,n\}$ and a second copy of $\{1,\dots,n\}$.
--
--   These are the objects of the LP duality theorem (Theorem 1.3.2) and of Propositions 1.3.2 and 1.3.3.
--
--   **Formalization Note** Vectors are functions from a finite index type to $\mathbb R$; $c^Tx$ is `c ⬝ᵥ x`, $Ax$ is `A *ᵥ x`, and $\le$ on vectors is the componentwise order. The book's optimal value $c^* \in [-\infty, +\infty]$ is never a Lean real number with a junk default: it appears only through the predicates "lower bound on $c^*$" (item 3) and "$v$ is the optimal value" (item 5, `IsGLB`/`IsLUB`), which no real satisfies when the value is infinite. "Solvable" is the existence of an optimal solution, which is the book's "feasible, bounded below, and the infimum is attained". No rank condition is imposed on $A$ (Lecture 1 has none).
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, pp. 1–2 (§1.1, (LP), feasible, bounded below, optimal value, solvable), p. 16 (lower bounds), p. 17 ((D), (LP∗)), p. 18 (proof of Theorem 1.3.2, (LP∗) in standard form)

import Mathlib

open Matrix

namespace ModernConvex.LPDuality

variable {m n : Type*} [Fintype m] [Fintype n]

/-- Feasible solution of the LP program `(LP) : min { cᵀx | Ax ≥ b }` (Ben-Tal–Nemirovski, p. 1):
a point `x` with `Ax − b ≥ 0` componentwise. -/
def PrimalFeasible (A : Matrix m n ℝ) (b : m → ℝ) (x : n → ℝ) : Prop :=
  b ≤ A *ᵥ x

/-- `(LP)` is feasible: its feasible set `{x | Ax − b ≥ 0}` is nonempty. -/
def PrimalIsFeasible (A : Matrix m n ℝ) (b : m → ℝ) : Prop :=
  ∃ x, PrimalFeasible A b x

/-- `(LP)` is bounded below: it is infeasible, or its objective `cᵀx` is bounded below on the
feasible set (p. 1). -/
def PrimalBoundedBelow (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ) : Prop :=
  ∃ L : ℝ, ∀ x, PrimalFeasible A b x → L ≤ c ⬝ᵥ x

/-- `a` is a lower bound on the optimal value `c*` of `(LP)`: `cᵀx ≥ a` whenever `Ax ≥ b`
(p. 16). For an infeasible program every real `a` is one (`c* = +∞`). -/
def IsPrimalLowerBound (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ) (a : ℝ) : Prop :=
  ∀ x, PrimalFeasible A b x → a ≤ c ⬝ᵥ x

/-- `x` is an optimal solution of `(LP)`: feasible, and `cᵀx ≤ cᵀx'` for every feasible `x'`. -/
def IsPrimalOptimal (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ) (x : n → ℝ) : Prop :=
  PrimalFeasible A b x ∧ ∀ x', PrimalFeasible A b x' → c ⬝ᵥ x ≤ c ⬝ᵥ x'

/-- `(LP)` is solvable: it has an optimal solution (feasible, bounded below, infimum attained;
p. 2). -/
def PrimalSolvable (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ) : Prop :=
  ∃ x, IsPrimalOptimal A b c x

/-- `v` is the (finite) optimal value `c* = inf {cᵀx | Ax ≥ b}` of `(LP)`: the greatest lower
bound of the objective values at feasible points. No real `v` qualifies when `(LP)` is
infeasible (`c* = +∞`) or unbounded below (`c* = −∞`). -/
def IsPrimalOptimalValue (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ) (v : ℝ) : Prop :=
  IsGLB {t : ℝ | ∃ x, PrimalFeasible A b x ∧ t = c ⬝ᵥ x} v

/-- Feasible solution of the dual `(LP∗) : max { bᵀy | Aᵀy = c, y ≥ 0 }` (p. 17). -/
def DualFeasible (A : Matrix m n ℝ) (c : n → ℝ) (y : m → ℝ) : Prop :=
  Aᵀ *ᵥ y = c ∧ 0 ≤ y

/-- `(LP∗)` is feasible. -/
def DualIsFeasible (A : Matrix m n ℝ) (c : n → ℝ) : Prop :=
  ∃ y, DualFeasible A c y

/-- `(LP∗)` is bounded above: its objective `bᵀy` is bounded above on its feasible set
(vacuously so when it is infeasible). -/
def DualBoundedAbove (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ) : Prop :=
  ∃ U : ℝ, ∀ y, DualFeasible A c y → b ⬝ᵥ y ≤ U

/-- `y` is an optimal solution of `(LP∗)`: dual feasible, and `bᵀy' ≤ bᵀy` for every dual
feasible `y'`. -/
def IsDualOptimal (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ) (y : m → ℝ) : Prop :=
  DualFeasible A c y ∧ ∀ y', DualFeasible A c y' → b ⬝ᵥ y' ≤ b ⬝ᵥ y

/-- `(LP∗)` is solvable: it has an optimal solution. -/
def DualSolvable (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ) : Prop :=
  ∃ y, IsDualOptimal A b c y

/-- `v` is the (finite) optimal value `sup {bᵀy | Aᵀy = c, y ≥ 0}` of `(LP∗)`: the least upper
bound of the dual objective values at dual feasible points. -/
def IsDualOptimalValue (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ) (v : ℝ) : Prop :=
  IsLUB {t : ℝ | ∃ y, DualFeasible A c y ∧ t = b ⬝ᵥ y} v

/-- The system `(D)` of p. 17 in the unknowns `(y, a)`: `y ≥ 0`, `Aᵀy = c`, `bᵀy ≥ a`. -/
def SystemD (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ) (y : m → ℝ) (a : ℝ) : Prop :=
  0 ≤ y ∧ Aᵀ *ᵥ y = c ∧ a ≤ b ⬝ᵥ y

/-- The constraint matrix of `(LP∗)` written in the `(LP)` form (proof of Theorem 1.3.2, p. 18):
the rows `[I_m; Aᵀ; −Aᵀ]`, so that `(LP∗)` is `min { −bᵀy | [I_m; Aᵀ; −Aᵀ] y − (0; c; −c) ≥ 0 }`. -/
def dualAsLPMatrix [DecidableEq m] (A : Matrix m n ℝ) : Matrix (m ⊕ (n ⊕ n)) m ℝ :=
  Matrix.fromRows (1 : Matrix m m ℝ) (Matrix.fromRows Aᵀ (-Aᵀ))

/-- The right-hand side `(0; c; −c)` of `(LP∗)` written in the `(LP)` form (p. 18). -/
def dualAsLPRhs (c : n → ℝ) : (m ⊕ (n ⊕ n)) → ℝ :=
  Sum.elim 0 (Sum.elim c (-c))

end ModernConvex.LPDuality


