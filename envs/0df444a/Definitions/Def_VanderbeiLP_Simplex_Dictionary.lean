-- Prove2me | Definitions.Def_VanderbeiLP_Simplex_Dictionary
-- name    : VanderbeiLP_Simplex_Dictionary
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T16:40:20.728772+00:00
-- url     : https://prove2.me/theorems/41444f09-6247-45d3-a109-2de166f2cfe8
-- title:
--   Dictionaries of a standard-form LP, determined by their basis
-- statement:
--   Consider the linear program in **standard form**
--   $$
--   \text{maximize } \sum_{j=1}^n c_j x_j \quad\text{subject to}\quad \sum_{j=1}^n a_{ij}x_j \le b_i\ (i = 1,\dots,m),\qquad x_j \ge 0\ (j = 1,\dots,n),
--   $$
--   with $m$ constraints and $n$ decision variables. Introducing the slack variables $w_i = b_i - \sum_j a_{ij}x_j$ and writing $x_{n+i} = w_i$, all $n+m$ variables are treated alike, and the constraints become the linear system $[A\ I]\,x = b$ in $x \in \mathbb{R}^{n+m}$.
--
--   A **dictionary** is specified by a set $\mathcal B \subseteq \{1,\dots,n+m\}$ of $m$ **basic** indices such that the columns of $[A\ I]$ indexed by $\mathcal B$ are linearly independent; $\mathcal N$ is the complementary set of **nonbasic** indices. Solving the system for the basic variables gives the dictionary
--   $$
--   \zeta = \bar\zeta + \sum_{j\in\mathcal N} \bar c_j x_j, \qquad x_i = \bar b_i - \sum_{j\in\mathcal N} \bar a_{ij} x_j \quad (i \in \mathcal B),
--   $$
--   where $\bar b_i$ and $\bar a_{ij}$ are the coordinates of $b$ and of the $j$-th column of $[A\ I]$ in the basis formed by the basic columns, $\bar c_j = c_j - \sum_{i\in\mathcal B} c_i \bar a_{ij}$ (with $c_j = 0$ for slack variables), and $\bar\zeta = \sum_{i\in\mathcal B} c_i \bar b_i$. Setting the nonbasic variables to zero gives the **basic solution** $x_i = \bar b_i$ ($i\in\mathcal B$), $x_j = 0$ ($j \in \mathcal N$). The dictionary is **feasible** if $\bar b_i \ge 0$ for all $i \in \mathcal B$, and **degenerate** if $\bar b_i = 0$ for some $i \in \mathcal B$.
--
--   Every coefficient is computed from $\mathcal B$, so a dictionary is completely determined by specifying which variables are basic. These objects are the states of the simplex method in every statement of the mission.
--
--   **Formalization Note** Variables are indexed by `Fin (n + m)`, decision variables first (`Fin.castAdd`) and slacks after them (`Fin.natAdd`), in Vanderbei's order $x_1,\dots,x_n,w_1,\dots,w_m$. The dictionary is a structure holding the basic set and proofs that it has $m$ elements and that its columns are linearly independent, so two dictionaries with the same basic set are equal. `bbar` and `abar` are extended by $0$ to nonbasic row indices; `D.bbar b` is the basic solution as a vector of all $n+m$ variables.
-- source:
--   Vanderbei, Linear Programming: Foundations and Extensions, 4th ed., Springer 2014, pp. 6–7 (PDF 25–26), standard form; p. 13 (PDF 31), §2.1.1 dictionaries and basic feasible solutions; p. 14 (PDF 32), Eqs. (2.5)–(2.6); p. 25 (PDF 42), definition of a degenerate dictionary

import Mathlib

namespace VanderbeiLP.Simplex

open Module

variable {m n : ℕ}

/-- Column `j` of the augmented constraint matrix `[A I]` of the standard-form problem
`maximize cᵀx s.t. Ax ≤ b, x ≥ 0` with slacks `w = b − Ax` (Vanderbei, p. 14, (2.5)).
Variables are indexed by `Fin (n + m)`: index `Fin.castAdd m j` is the decision variable
`x_{j+1}`, index `Fin.natAdd n i` is the slack `x_{n+i+1} = w_{i+1}`. The column of a decision
variable is the corresponding column of `A`; the column of the slack `w_i` is the unit vector
`e_i`. -/
def augCol (A : Matrix (Fin m) (Fin n) ℝ) (j : Fin (n + m)) : Fin m → ℝ :=
  Fin.addCases (motive := fun _ => Fin m → ℝ) (fun k i => A i k) (fun k => Pi.single k 1) j

/-- The objective coefficients extended to all `n + m` variables: `c_j` for a decision variable,
`0` for a slack variable. -/
def extCost (c : Fin n → ℝ) (j : Fin (n + m)) : ℝ :=
  Fin.addCases (motive := fun _ => ℝ) c (fun _ => 0) j

/-- A **dictionary** of the standard-form problem with constraint matrix `A` (Vanderbei,
p. 14, (2.6)), recorded by its set `B` of basic variables. The set has exactly `m` elements and
the corresponding columns of `[A I]` are linearly independent, so that the system
`[A I] x = b` can be solved for the basic variables in terms of the nonbasic ones. Every
coefficient of the dictionary is computed from `B` below; a dictionary is therefore
completely determined by which variables are basic. -/
structure Dictionary (A : Matrix (Fin m) (Fin n) ℝ) where
  /-- The set of indices of the basic variables. -/
  B : Finset (Fin (n + m))
  card_B : B.card = m
  linearIndependent : LinearIndependent ℝ (fun j : B => augCol A (j : Fin (n + m)))

namespace Dictionary

variable {A : Matrix (Fin m) (Fin n) ℝ}

/-- The basic columns of `[A I]`, as a basis of `ℝ^m`. -/
noncomputable def colBasis (D : Dictionary A) : Basis D.B ℝ (Fin m → ℝ) :=
  basisOfLinearIndependentOfCardEqFinrank' _ D.linearIndependent
    (by simp [D.card_B])

/-- The right-hand side `b̄` of the dictionary, extended by `0` to the nonbasic variables:
for `i ∈ B`, `b̄_i` is the value of the basic variable `x_i` when all nonbasic variables are
zero. The vector `D.bbar b` is the basic solution of the dictionary (all `n + m` variables). -/
noncomputable def bbar (D : Dictionary A) (b : Fin m → ℝ) (i : Fin (n + m)) : ℝ :=
  if h : i ∈ D.B then D.colBasis.repr b ⟨i, h⟩ else 0

/-- The coefficient `ā_{ij}` of the dictionary: for `i ∈ B` the row of `x_i` reads
`x_i = b̄_i − ∑_{j ∈ N} ā_{ij} x_j`. It is `0` for `i ∉ B`. -/
noncomputable def abar (D : Dictionary A) (i j : Fin (n + m)) : ℝ :=
  if h : i ∈ D.B then D.colBasis.repr (augCol A j) ⟨i, h⟩ else 0

/-- The objective coefficient `c̄_j` of the dictionary, `ζ = ζ̄ + ∑_{j ∈ N} c̄_j x_j`
(it vanishes for basic `j`). -/
noncomputable def cbar (D : Dictionary A) (c : Fin n → ℝ) (j : Fin (n + m)) : ℝ :=
  extCost c j - ∑ i ∈ D.B, extCost c i * D.abar i j

/-- The constant `ζ̄` of the objective row: the objective value of the basic solution. -/
noncomputable def zetaBar (D : Dictionary A) (b : Fin m → ℝ) (c : Fin n → ℝ) : ℝ :=
  ∑ i ∈ D.B, extCost c i * D.bbar b i

/-- A dictionary is **feasible** when every basic variable has a nonnegative value,
`b̄_i ≥ 0` for all `i ∈ B`. -/
def IsFeasible (D : Dictionary A) (b : Fin m → ℝ) : Prop :=
  ∀ i ∈ D.B, 0 ≤ D.bbar b i

/-- A dictionary is **degenerate** when `b̄_i = 0` for some `i ∈ B` (p. 25). -/
def IsDegenerate (D : Dictionary A) (b : Fin m → ℝ) : Prop :=
  ∃ i ∈ D.B, D.bbar b i = 0

end Dictionary

end VanderbeiLP.Simplex


