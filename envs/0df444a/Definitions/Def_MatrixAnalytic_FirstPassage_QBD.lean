-- Prove2me | Definitions.Def_MatrixAnalytic_FirstPassage_QBD
-- name    : MatrixAnalytic_FirstPassage_QBD
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:46:07.140274+00:00
-- url     : https://prove2.me/theorems/e1251aac-36ab-41ab-8e14-4d867fde8435
-- title:
--   The finite homogeneous QBD (10.2) on levels 0, …, M and its standing assumptions
-- statement:
--   Fix an integer $M\ge1$ and a finite set $\iota$ of $m$ **phases**. The states are the pairs $(n,i)$ with **level** $0\le n\le M$ and phase $i\in\iota$; the level $\ell(n)$ is the set $\{(n,i): i\in\iota\}$. Given $m\times m$ real matrices $P_{00},A_0,A_1,A_2,P_{MM}$, the **finite QBD** is the Markov chain with block-tridiagonal transition matrix
--   $$P=\begin{bmatrix}P_{00}&A_0&&&\\A_2&A_1&A_0&&\\&\ddots&\ddots&\ddots&\\&&A_2&A_1&A_0\\&&&A_2&P_{MM}\end{bmatrix}:$$
--   from level $n$ it moves up one level with the probabilities $A_0$, down one level with $A_2$, and stays in its level with $P_{00}$ at level $0$, $P_{MM}$ at level $M$ and $A_1$ at the levels $1,\dots,M-1$; all other transitions have probability $0$.
--
--   The standing assumptions of Chapters 10 and 11 are collected in the predicate *finite QBD*: $M\ge1$; all five blocks are entrywise nonnegative; $P$ is stochastic, i.e. $P_{00}\mathbf 1+A_0\mathbf 1=\mathbf 1$, $A_2\mathbf 1+A_1\mathbf 1+A_0\mathbf 1=\mathbf 1$ (required when $M\ge2$, the only case with intermediate levels) and $A_2\mathbf 1+P_{MM}\mathbf 1=\mathbf 1$; and the chain is irreducible on its $(M+1)m$ states.
--
--   **Formalization Note** States are encoded as `ℕ × ι`; every transition from or to a level above $M$ is given probability $0$, and those states are never reached from a level $\le M$. The phase set is a `Fintype`: Chapters 10–11 work with finite matrices ($1\le i\le m$, LU decompositions, matrix inverses).
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 222, Eq. (10.2) (Chapter 10, the setting of Chapter 11); irreducibility as used on pp. 246–247

import Mathlib
import Definitions.Def_MatrixAnalytic_FirstPassage_Chain

namespace MatrixAnalytic.FirstPassage

noncomputable section

/-!
The finite homogeneous QBD of Chapter 10 of Latouche & Ramaswami (p. 222, Eq. (10.2)), the
setting of Chapter 11: a Markov chain on the states `(n, i)` with level `0 ≤ n ≤ M` and phase
`i` in a finite set `ι` (`m = |ι|`), with block-tridiagonal transition matrix
```
      ⎡ P₀₀ A₀            ⎤
      ⎢ A₂  A₁  A₀        ⎥
  P = ⎢     ⋱   ⋱   ⋱     ⎥
      ⎢         A₂  A₁ A₀ ⎥
      ⎣             A₂ P_MM⎦
```
States are encoded as `ℕ × ι`; every transition from or to a level above `M` has probability `0`
(those states are never visited from a level `≤ M`).
-/

variable {ι : Type*}

/-- The level `ℓ(n) = {(n, 1), …, (n, m)}`. -/
def level (n : ℕ) : Set (ℕ × ι) := {x | x.1 = n}

/-- The transition matrix (10.2) of the finite QBD with levels `0, …, M` (`M ≥ 1`) and blocks
`P₀₀, A₀, A₁, A₂, P_MM`: up one level with `A₀`, down one level with `A₂`, within the level with
`P₀₀` at level `0`, `P_MM` at level `M` and `A₁` at the levels `1, …, M − 1`; all other entries,
and all entries involving a level above `M`, are `0`. -/
def finiteQBD (M : ℕ) (P₀₀ A₀ A₁ A₂ P_MM : Matrix ι ι ℝ) : ℕ × ι → ℕ × ι → ℝ :=
  fun x y =>
    if x.1 ≤ M ∧ y.1 ≤ M then
      if y.1 = x.1 + 1 then A₀ x.2 y.2
      else if y.1 + 1 = x.1 then A₂ x.2 y.2
      else if y.1 = x.1 then
        (if x.1 = 0 then P₀₀ x.2 y.2 else if x.1 = M then P_MM x.2 y.2 else A₁ x.2 y.2)
      else 0
    else 0

/-- The standing assumptions of Chapters 10–11: `M ≥ 1`, the matrix (10.2) is a transition
matrix (nonnegative blocks, every row summing to `1`: `P₀₀1 + A₀1 = 1`, `A₂1 + A₁1 + A₀1 = 1`
when there are intermediate levels, `A₂1 + P_MM1 = 1`), and the chain is irreducible on the
states of levels `0, …, M`. -/
structure IsFiniteQBD [Fintype ι] (M : ℕ) (P₀₀ A₀ A₁ A₂ P_MM : Matrix ι ι ℝ) : Prop where
  one_le : 1 ≤ M
  nonneg_P₀₀ : ∀ i j, 0 ≤ P₀₀ i j
  nonneg_A₀ : ∀ i j, 0 ≤ A₀ i j
  nonneg_A₁ : ∀ i j, 0 ≤ A₁ i j
  nonneg_A₂ : ∀ i j, 0 ≤ A₂ i j
  nonneg_P_MM : ∀ i j, 0 ≤ P_MM i j
  row_zero : ∀ i, ∑ j, (P₀₀ i j + A₀ i j) = 1
  row_mid : 2 ≤ M → ∀ i, ∑ j, (A₂ i j + A₁ i j + A₀ i j) = 1
  row_top : ∀ i, ∑ j, (A₂ i j + P_MM i j) = 1
  irreducible : IrreducibleOn (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) {x | x.1 ≤ M}

end

end MatrixAnalytic.FirstPassage


