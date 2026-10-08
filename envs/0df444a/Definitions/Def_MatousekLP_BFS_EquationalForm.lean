-- Prove2me | Definitions.Def_MatousekLP_BFS_EquationalForm
-- name    : MatousekLP_BFS_EquationalForm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T10:41:25.434265+00:00
-- url     : https://prove2.me/theorems/07974bda-d85c-4ac7-add8-a0938ea9149d
-- title:
--   Linear programs in equational form: feasible, optimal and basic feasible solutions, vertices
-- statement:
--   This module fixes the vocabulary of Chapter 4 of Matoušek & Gärtner for a linear program in **equational form**
--
--   $$\text{maximize } c^{T}x \quad \text{subject to } Ax = b,\ x \ge 0,$$
--
--   where $A$ is a real $m\times n$ matrix, $b\in\mathbb{R}^m$ and $c\in\mathbb{R}^n$; the inequality $x\ge 0$ is componentwise.
--
--   1. A **feasible solution** is a vector $x\in\mathbb{R}^n$ with $Ax=b$ and $x\ge 0$; the **feasible set** is the set $P$ of all of them.
--   2. An **optimal solution** is a feasible $x$ with $c^{T}y\le c^{T}x$ for every feasible $y$.
--   3. The objective is **bounded from above** on the feasible set if there is a real $M$ with $c^{T}x\le M$ for every feasible $x$.
--   4. For $S\subseteq\{1,\dots,n\}$, $A_S$ is the matrix formed by the columns of $A$ indexed by $S$. A **basis** is an $m$-element set $B\subseteq\{1,\dots,n\}$ such that the columns of $A_B$ are linearly independent, i.e. the square matrix $A_B$ is nonsingular.
--   5. A **basic feasible solution** is a feasible $x$ for which some basis $B$ satisfies $x_j=0$ for all $j\notin B$.
--   6. For a vector $x$, $K(x)=\{j : x_j>0\}$ is its set of positive coordinates.
--   7. A point $v$ is a **vertex** of a set $P\subseteq\mathbb{R}^n$ if $v\in P$ and there is a nonzero $c\in\mathbb{R}^n$ with $c^{T}v>c^{T}y$ for every $y\in P\setminus\{v\}$, i.e. $v$ is the unique maximizer over $P$ of some nonzero linear function.
--
--   These are the objects in which the simplex method of Chapter 5 and the later chapters of the book state their results; basic feasible solutions depend only on $A$ and $b$, not on $c$.
--
--   **Formalization Note** Vectors are functions `Fin n → ℝ`, so the book's indices $1,\dots,n$ become $0,\dots,n-1$. Linear independence of the columns of $A_S$ is `LinearIndependent ℝ` of the family of columns indexed by the elements of the finset $S$. Optimality and boundedness are stated against every feasible point; no supremum is used. The rank assumption of §4.2 is not part of these definitions; it is a hypothesis of each theorem that uses them.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 41 (§4.1, equational form), p. 3 (§1.1, feasible/optimal solution), p. 44 (§4.2, basic feasible solution), p. 46 (basis), p. 45 (Lemma 4.2.1, the set K), p. 53 (§4.4, vertex)

import Mathlib

namespace MatousekLP.BFS

/-!
# Linear programs in equational form, basic feasible solutions, vertices

Matoušek & Gärtner, *Understanding and Using Linear Programming*, Springer 2007:
§4.1 (p. 41) equational form, §1.1 (p. 3) feasible and optimal solutions,
§4.2 (p. 44) basic feasible solutions, §4.4 (p. 53) vertices.

The linear program is `maximize cᵀx subject to Ax = b, x ≥ 0` with
`A : Matrix (Fin m) (Fin n) ℝ`, `b : Fin m → ℝ`, `c : Fin n → ℝ`.
The book's indices `1, …, n` are `0, …, n-1` here.
-/

open Matrix

variable {m n : ℕ}

/-- `x` is a feasible solution of the equational-form LP: `Ax = b` and `x ≥ 0` (p. 41). -/
def IsFeasible (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) : Prop :=
  A *ᵥ x = b ∧ 0 ≤ x

/-- The set of all feasible solutions `{x ∈ ℝⁿ : Ax = b, x ≥ 0}`. -/
def feasibleSet (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) : Set (Fin n → ℝ) :=
  {x | IsFeasible A b x}

/-- `x` is an optimal solution of `maximize cᵀx subject to Ax = b, x ≥ 0`: it is feasible and
`cᵀy ≤ cᵀx` for every feasible `y` (p. 3). -/
def IsOptimal (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : Fin n → ℝ) : Prop :=
  IsFeasible A b x ∧ ∀ y, IsFeasible A b y → c ⬝ᵥ y ≤ c ⬝ᵥ x

/-- The objective function `cᵀx` is bounded from above on the set of feasible solutions. -/
def IsBoundedAbove (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) : Prop :=
  ∃ M : ℝ, ∀ x, IsFeasible A b x → c ⬝ᵥ x ≤ M

/-- The columns of `A` indexed by `S ⊆ {1, …, n}` (the columns of the matrix `A_S`) are
linearly independent. -/
def ColumnsLinIndep (A : Matrix (Fin m) (Fin n) ℝ) (S : Finset (Fin n)) : Prop :=
  LinearIndependent ℝ (fun j : S => fun i : Fin m => A i (j : Fin n))

/-- A **basis** (p. 46): an `m`-element set `B ⊆ {1, …, n}` with `A_B` nonsingular, i.e. the
columns of `A` indexed by `B` are linearly independent. -/
def IsBasis (A : Matrix (Fin m) (Fin n) ℝ) (B : Finset (Fin n)) : Prop :=
  B.card = m ∧ ColumnsLinIndep A B

/-- A **basic feasible solution** (p. 44): a feasible solution `x` for which there is an
`m`-element set `B` with `A_B` nonsingular and `x_j = 0` for all `j ∉ B`. -/
def IsBasicFeasible (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) : Prop :=
  IsFeasible A b x ∧ ∃ B : Finset (Fin n), IsBasis A B ∧ ∀ j, j ∉ B → x j = 0

/-- The index set `K = {j : x_j > 0}` of Lemma 4.2.1 (p. 45). -/
noncomputable def positiveIndices (x : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => 0 < x j)

/-- A **vertex** of `P ⊆ ℝⁿ` (p. 53): `v ∈ P` and there is a nonzero `c ∈ ℝⁿ` with
`cᵀv > cᵀy` for all `y ∈ P \ {v}`. -/
def IsVertex (P : Set (Fin n → ℝ)) (v : Fin n → ℝ) : Prop :=
  v ∈ P ∧ ∃ c : Fin n → ℝ, c ≠ 0 ∧ ∀ y ∈ P, y ≠ v → c ⬝ᵥ y < c ⬝ᵥ v

end MatousekLP.BFS


