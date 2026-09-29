-- Prove2me | Definitions.Def_BealeConvexMin_QuadSimplex_Tableau
-- name    : BealeConvexMin_QuadSimplex_Tableau
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:31:14.061279+00:00
-- url     : https://prove2.me/theorems/4ba55c4d-bb69-4f94-afb3-e2eae33cdf77
-- title:
--   Beale (1955), eq. (2.3): the tableau of restricted and free nonbasic variables, standard form
-- statement:
--   This file fixes the state of Beale's simplex iteration for a quadratic objective.
--
--   There are $n$ **restricted** variables $x_j\ge 0$ and $N=n-m$ nonbasic slots. Each nonbasic slot holds either a restricted variable or a **free** variable (a linear function of the $x_j$ that is not restricted in sign). Every restricted variable is written as an affine function of the nonbasic variables,
--   $$x_h=a_{h0}+\sum_{l=1}^{N}a_{hl}z_l,\tag{2.3}$$
--   and the objective is $C=\sum_{k,l=0}^{N}c_{kl}z_kz_l$ with $z_0=1$ (eq. (3.1)).
--
--   1. A **tableau** consists of the slot labels (restricted variable $x_j$, or free), the rows $(a_{h0},\dots,a_{hN})$ of all $n$ restricted variables, and the matrix $(c_{kl})$. Free variables have no row: once a free variable leaves the nonbasic set its defining equation is dropped.
--   2. $x_j$ is **basic** if it occupies no slot. The labels are **consistent** if no restricted variable occupies two slots and a restricted variable in slot $k$ has the unit row $x_j=z_k$.
--   3. **Positivity of the basic variables**: $a_{h0}>0$ for every basic $x_h$. This is the effect of Charnes's $\varepsilon$-perturbations, "We ensure that the $a_{h0}$ are always positive, and not zero".
--   4. $s$ is the number of nonbasic free variables, and the **restricted nonbasic set** is the set of restricted variables that occupy a slot.
--   5. $C$ is in **standard form** when it contains no linear term in any free variable: $c_{k0}=0$ for every slot $k$ holding a free variable.
--
--   In the associated solution every nonbasic variable is zero, so $x_h=a_{h0}$ and $C=c_{00}$.
--
--   **Formalization Note** The problem data $A,B$ of (2.1) are not part of the tableau: the iteration starts from a tableau already in the form (2.3), and phase 1 (artificial variables, M-method) is out of scope. Restricted variables are indexed by `Fin n` (the paper's $x_1,\dots,x_n$ shifted by one). Nonbasic slot `k : Fin N` is matrix index `k.succ`; index `0` is $z_0=1$. The positivity of item 3 is a property of a tableau and is applied only to basic variables, since nonbasic ones vanish in the associated solution.
-- source:
--   Beale, On Minimizing a Convex Function Subject to Linear Inequalities, J. R. Statist. Soc. B 17(2), 1955, https://doi.org/10.1111/j.2517-6161.1955.tb00191.x, p. 174 (PDF p. 2), eq. (2.3) and the two paragraphs after it; p. 175 (PDF p. 3), eq. (3.1); p. 177 (PDF p. 5), definition of standard form

import Mathlib
import Definitions.Def_BealeConvexMin_QuadSimplex_pivotC

namespace BealeConvexMin.QuadSimplex

/-!
Beale (1955), §2, p. 174, eq. (2.3), and §3, p. 175, eq. (3.1): the state of the iteration for a
quadratic `C`.

There are `n` restricted variables, indexed by `Fin n` (index `j` is the paper's `x_{j+1}`),
and `N` nonbasic slots (the paper's `N = n - m`). Slot `0` of `Fin (N+1)` is the constant `z_0 = 1`; the nonbasic slot with index
`k : Fin N` is slot `k.succ` (the paper's `z_{k+1}`).
-/

/-- A tableau (§2, eq. (2.3); §3, eq. (3.1)).
* `lab k` says which variable occupies nonbasic slot `k.succ`: `some j` for the restricted
  variable `x_j`, `none` for a free variable (a linear function of the `x_j` with no sign
  restriction, p. 174).
* `row j` expresses the restricted variable `x_j` as `x_j = Σ_{l=0}^{N} row j l · z_l`
  (eq. (2.3), `a_h0 = row h 0`). Every restricted variable has a row; a nonbasic one has the unit
  row. Free variables have no row (p. 175: "it is not normally necessary to retain the equation
  defining a free variable once that variable has ceased to be nonbasic").
* `c` is the matrix `(c_kl)` of eq. (3.1), `C = Σ_{k,l} c_kl z_k z_l` with `z_0 = 1`. -/
structure Tableau (n N : ℕ) where
  lab : Fin N → Option (Fin n)
  row : Fin n → Fin (N + 1) → ℝ
  c : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ

variable {n N : ℕ}

/-- `x_j` is basic: it occupies no nonbasic slot. -/
def IsBasic (T : Tableau n N) (j : Fin n) : Prop :=
  ∀ k : Fin N, T.lab k ≠ some j

/-- The labelling is consistent: no restricted variable occupies two slots, and the row of a
nonbasic restricted variable `x_j` in slot `k.succ` is the unit row `x_j = z_{k+1}`. -/
def LabelsConsistent (T : Tableau n N) : Prop :=
  (∀ k k' : Fin N, ∀ j : Fin n, T.lab k = some j → T.lab k' = some j → k = k') ∧
  ∀ (k : Fin N) (j : Fin n), T.lab k = some j → T.row j = Pi.single k.succ 1

/-- The ε-perturbation device (p. 174: "We ensure that the `a_h0` are always positive, and not
zero"), stated as a property of one tableau: every basic restricted variable is strictly positive
in the associated solution (`a_h0 = row h 0 > 0`). Nonbasic variables vanish in the associated
solution and are not constrained. -/
def BasicPositive (T : Tableau n N) : Prop :=
  ∀ j : Fin n, IsBasic T j → 0 < T.row j 0

/-- `s`, the number of nonbasic free variables (p. 174, after (2.3)). -/
def numFree (T : Tableau n N) : ℕ :=
  (Finset.univ.filter fun k : Fin N => T.lab k = none).card

/-- The set of restricted nonbasic variables. -/
def restrictedNonbasic (T : Tableau n N) : Set (Fin n) :=
  {j | ∃ k : Fin N, T.lab k = some j}

/-- Standard form (§3, p. 177): `C` contains no linear term in any free variable, i.e.
`c_k0 = 0` for every nonbasic slot `k` holding a free variable. -/
def IsStandardForm (T : Tableau n N) : Prop :=
  ∀ k : Fin N, T.lab k = none → T.c k.succ 0 = 0

end BealeConvexMin.QuadSimplex


