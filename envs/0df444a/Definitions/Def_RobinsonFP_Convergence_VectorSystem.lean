-- Prove2me | Definitions.Def_RobinsonFP_Convergence_VectorSystem
-- name    : RobinsonFP_Convergence_VectorSystem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:36:45.674624+00:00
-- url     : https://prove2.me/theorems/f428ebf1-b560-4a26-84e0-72c6bc134490
-- title:
--   Definitions 1–2 and p. 296 — vector systems, eligibility, and the solution and value of a matrix game
-- statement:
--   Let $A = (a_{ij})$ be a real $m \times n$ matrix, the pay-off matrix of a finite two-person zero-sum game: the first player chooses a row $i$, the second player simultaneously chooses a column $j$, and the second player pays the first $a_{ij}$. Write $A_{i\cdot}$ for the $i$-th row of $A$ (a vector with $n$ components) and $A_{\cdot j}$ for the $j$-th column (a vector with $m$ components). For a vector $W$ with finitely many components $w_1, w_2, \dots$, write
--   $$\max W = \max_j w_j, \qquad \min W = \min_j w_j .$$
--
--   1. **Solution and value** (p. 296). A pair of probability vectors $X = (x_1,\dots,x_m)$, $Y = (y_1,\dots,y_n)$ (that is, $x_i \ge 0$, $\sum_i x_i = 1$, $y_j \ge 0$, $\sum_j y_j = 1$) is a **solution** of the game with **value** $v$ if
--   $$\min_j \sum_i a_{ij} x_i \;=\; v \;=\; \max_i \sum_j a_{ij} y_j .$$
--   By the minimax theorem such a pair exists for every matrix $A$.
--
--   2. **Vector system** (Definition 1). A pair $(U, V)$ consisting of a sequence $U(0), U(1), \dots$ of $n$-dimensional vectors and a sequence $V(0), V(1), \dots$ of $m$-dimensional vectors is a **vector system for $A$** if $\min U(0) = \max V(0)$ and, for every $t = 0, 1, 2, \dots$,
--   $$U(t+1) = U(t) + A_{i\cdot}, \qquad V(t+1) = V(t) + A_{\cdot j},$$
--   where the row $i$ and the column $j$ satisfy $v_i(t) = \max V(t)$ and $u_j(t) = \min U(t)$. The row added to $U$ is chosen at a largest component of $V$, the column added to $V$ at a smallest component of $U$.
--
--   3. **Alternate vector system** (p. 297). The same, except that the column $j$ is chosen after $U$ has been updated: $u_j(t+1) = \min U(t+1)$.
--
--   4. **Eligibility** (Definition 2). Row $i$ is **eligible in the interval $(t, t')$** if $v_i(t_1) = \max V(t_1)$ for some integer $t_1$ with $t \le t_1 \le t'$; column $j$ is eligible in $(t, t')$ if $u_j(t_2) = \min U(t_2)$ for some $t \le t_2 \le t'$.
--
--   The vector system is Brown's iterative method (fictitious play): $U(t)/t$ and $V(t)/t$ are, up to the initial vectors, the payoffs against the empirical mixed strategies of the two players. These definitions are shared by every statement of the mission.
--
--   **Formalization Note** Rows are indexed by a finite nonempty type `ι` and columns by a finite nonempty type `κ` (so $m, n \ge 1$; `Fin m`, `Fin n` is a special case). $\max W$ and $\min W$ are `Finset.sup'` and `Finset.inf'` over all indices, hence attained. Time is a natural number. A vector system allows any choice among tied maximizing rows and minimizing columns at each step, which the existential `∃ i j` per step expresses; no tie-breaking rule is fixed. The interval $(t, t')$ of Definition 2 is the closed integer interval $t \le t_1 \le t'$, as printed. The solution is a predicate `IsSolution A x y v` relating the two probability vectors to the number $v$.
-- source:
--   Robinson, An Iterative Method of Solving a Game, Ann. of Math. 54(2) (1951), DOI 10.2307/1969530, pp. 296–298: value and solution (p. 296), Definition 1 (pp. 296–297), alternate notion (p. 297), Definition 2 (p. 298)

import Mathlib

namespace RobinsonFP.Convergence

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- `max V = max_j v_j` of a vector with finitely many, and at least one, components
(Robinson 1951, p. 296). The maximum is attained. -/
noncomputable def vmax [Nonempty ι] (w : ι → ℝ) : ℝ := Finset.univ.sup' Finset.univ_nonempty w

/-- `min V = min_j v_j` of a vector with finitely many, and at least one, components
(Robinson 1951, p. 296). The minimum is attained. -/
noncomputable def vmin [Nonempty ι] (w : ι → ℝ) : ℝ := Finset.univ.inf' Finset.univ_nonempty w

/-- Definition 1 (Robinson 1951, pp. 296–297): `(U, V)` is a vector system for the `m × n` matrix
`A`. Rows are indexed by `ι` (m of them), columns by `κ` (n of them). `U t : κ → ℝ` is
n-dimensional and is increased by a row `A i = A_{i·}`; `V t : ι → ℝ` is m-dimensional and is
increased by a column `fun k => A k j = A_{·j}`. At each step `t` the row `i` maximizes `V t` and
the column `j` minimizes `U t`; ties may be broken arbitrarily, step by step. -/
def IsVectorSystem [Nonempty ι] [Nonempty κ] (A : Matrix ι κ ℝ)
    (U : ℕ → κ → ℝ) (V : ℕ → ι → ℝ) : Prop :=
  vmin (U 0) = vmax (V 0) ∧
  ∀ t, ∃ i j, V t i = vmax (V t) ∧ U t j = vmin (U t) ∧
    U (t + 1) = U t + A i ∧ V (t + 1) = V t + fun k => A k j

/-- The alternate notion of vector system (Robinson 1951, p. 297): as in Definition 1, except
that the column `j` minimizes the updated vector `U (t + 1)`. -/
def IsAltVectorSystem [Nonempty ι] [Nonempty κ] (A : Matrix ι κ ℝ)
    (U : ℕ → κ → ℝ) (V : ℕ → ι → ℝ) : Prop :=
  vmin (U 0) = vmax (V 0) ∧
  ∀ t, ∃ i j, V t i = vmax (V t) ∧ U (t + 1) = U t + A i ∧
    U (t + 1) j = vmin (U (t + 1)) ∧ V (t + 1) = V t + fun k => A k j

/-- Definition 2, rows (Robinson 1951, p. 298): row `i` is eligible in the interval `(t, t')`,
i.e. `v_i(t₁) = max V(t₁)` for some `t ≤ t₁ ≤ t'`. -/
def RowEligible [Nonempty ι] (V : ℕ → ι → ℝ) (i : ι) (t t' : ℕ) : Prop :=
  ∃ t₁, t ≤ t₁ ∧ t₁ ≤ t' ∧ V t₁ i = vmax (V t₁)

/-- Definition 2, columns (Robinson 1951, p. 298): column `j` is eligible in the interval
`(t, t')`, i.e. `u_j(t₂) = min U(t₂)` for some `t ≤ t₂ ≤ t'`. -/
def ColEligible [Nonempty κ] (U : ℕ → κ → ℝ) (j : κ) (t t' : ℕ) : Prop :=
  ∃ t₂, t ≤ t₂ ∧ t₂ ≤ t' ∧ U t₂ j = vmin (U t₂)

/-- A solution `(X, Y)` of the matrix game `A` with value `v` (Robinson 1951, p. 296): `x`, `y` are
probability vectors and equality holds in (1),
`min_j Σ_i a_ij x_i = v = max_i Σ_j a_ij y_j`. -/
def IsSolution [Nonempty ι] [Nonempty κ] (A : Matrix ι κ ℝ) (x : ι → ℝ) (y : κ → ℝ) (v : ℝ) :
    Prop :=
  x ∈ stdSimplex ℝ ι ∧ y ∈ stdSimplex ℝ κ ∧
  vmin (fun j => ∑ i, A i j * x i) = v ∧ vmax (fun i => ∑ j, A i j * y j) = v

end RobinsonFP.Convergence


