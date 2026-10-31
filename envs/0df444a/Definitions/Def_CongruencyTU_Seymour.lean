-- Prove2me | Definitions.Def_CongruencyTU_Seymour
-- name    : CongruencyTU_Seymour
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:45:39.279616+00:00
-- url     : https://prove2.me/theorems/35dc66a1-70f0-434a-8b4c-91f259fbaab2
-- title:
--   The four cases of Seymour's TU decomposition (Theorem 14)
-- statement:
--   For a totally unimodular $T\in\mathbb Z^{k\times n}$ the four cases of Theorem 14 are:
--
--   1. $T$ or $T^\top$ is a network matrix;
--   2. after deleting rows and columns with at most one non-zero entry, rows and columns that appear twice or whose negation appears, and changing signs of rows and columns, $T$ equals
--   $$R_{10}=\begin{pmatrix}1&-1&0&0&-1\\-1&1&-1&0&0\\0&-1&1&-1&0\\0&0&-1&1&-1\\-1&0&0&-1&1\end{pmatrix}\quad\text{or}\quad\begin{pmatrix}1&1&1&1&1\\1&1&1&0&0\\1&0&1&1&0\\1&0&0&1&1\\1&1&0&0&1\end{pmatrix};$$
--   3. after row and column permutations, $T$ is a 1-, 2- or 3-sum of totally unimodular matrices with $n_A,n_B\ge 2$;
--   4. after pivoting once (on a non-zero entry) and permuting, $T$ is a 3-sum of totally unimodular matrices with $n_A,n_B\ge2$.
--
--   Cases 1 and 2 are the **base blocks**. A correct output of the decomposition algorithm names a case that holds together with its data: which of $T$, $T^\top$ is a network matrix; which $5\times5$ matrix; the decomposition; or the pivot entry and the decomposition of the pivoted matrix.
--
--   **Formalization Note** Sign changes commute with deletions. The surviving $5\times 5$ submatrix is matched with the displayed matrix up to the order in which its rows and columns are listed.
-- source:
--   Nägele, Santiago, Zenklusen, Congruency-Constrained TU Problems Beyond the Bimodular Case, arXiv:2109.03148v3 [math.OC] (preprint, 25 Apr 2023), https://arxiv.org/abs/2109.03148v3, Theorem 14, p.8 (PDF p.9)

import Mathlib
import Definitions.Def_CongruencyTU_Sums
import Definitions.Def_CongruencyTU_Network
import Definitions.Def_CongruencyTU_Core

namespace CongruencyTU

/-! # The four cases of Seymour's TU decomposition (Theorem 14)

Nägele–Santiago–Zenklusen, arXiv:2109.03148v3 (preprint), Theorem 14, p.8 (PDF p.9):
(i) `T` or `T⊤` is a network matrix; (ii) `T` is, possibly after iteratively deleting a row or
column with at most one non-zero entry, deleting a row or column that appears twice or whose
negation also appears, and changing the sign of a row or column, equal to one of two `5 × 5`
matrices; (iii) `T` can, possibly after row and column permutations, be decomposed into a 1-, 2-, or
3-sum of totally unimodular matrices with `nA, nB ≥ 2`; (iv) `T` can, after pivoting once and
possibly performing row and column permutations, be decomposed into a 3-sum of totally unimodular
matrices with `nA, nB ≥ 2`. Cases (i) and (ii) are the *base block* matrices.

**Formalization Note.** Sign changes commute with the deletions (both deletion rules are invariant
under negating a row or a column), so case (ii) is: some submatrix reachable by deletions equals one
of the two matrices after negating some of its rows and columns. The remaining `5 × 5` submatrix is
matched with the displayed matrix through bijections of its rows and columns with `Fin 5`: the
paper's "equal to" is read up to the order in which the surviving rows and columns are listed
(otherwise a row-swapped copy of the first matrix, which is TU, would fall into none of the cases).
Pivoting in (iv) is on a non-zero (hence `±1`) entry. -/

/-- The first matrix of Theorem 14 (ii) (the matrix `R₁₀`). -/
def baseR10 : Matrix (Fin 5) (Fin 5) ℤ :=
  !![1, -1, 0, 0, -1; -1, 1, -1, 0, 0; 0, -1, 1, -1, 0; 0, 0, -1, 1, -1; -1, 0, 0, -1, 1]

/-- The second matrix of Theorem 14 (ii). -/
def baseR12 : Matrix (Fin 5) (Fin 5) ℤ :=
  !![1, 1, 1, 1, 1; 1, 1, 1, 0, 0; 1, 0, 1, 1, 0; 1, 0, 0, 1, 1; 1, 1, 0, 0, 1]

variable {k n : ℕ}

/-- `T` reduces, by deletions and sign changes of rows and columns, to the `5 × 5` matrix `M`. -/
def ReducesTo (T : Matrix (Fin k) (Fin n) ℤ) (M : Matrix (Fin 5) (Fin 5) ℤ) : Prop :=
  ∃ c, DelReachable T c ∧ ∃ (σ : Fin 5 → Fin k) (τ : Fin 5 → Fin n),
    Function.Injective σ ∧ Function.Injective τ ∧
    Set.range σ = (c.1 : Set (Fin k)) ∧ Set.range τ = (c.2 : Set (Fin n)) ∧
    ∃ s t : Fin 5 → ℤ, (∀ i, s i = 1 ∨ s i = -1) ∧ (∀ j, t j = 1 ∨ t j = -1) ∧
      ∀ i j, s i * t j * T (σ i) (τ j) = M i j

/-- Case (i) of Theorem 14: `T` or `T⊤` is a network matrix. -/
def SeymourCase1 (T : Matrix (Fin k) (Fin n) ℤ) : Prop :=
  IsNetworkMatrix T ∨ IsNetworkMatrix T.transpose

/-- Case (ii) of Theorem 14. -/
def SeymourCase2 (T : Matrix (Fin k) (Fin n) ℤ) : Prop :=
  ReducesTo T baseR10 ∨ ReducesTo T baseR12

/-- Case (iii) of Theorem 14. -/
def SeymourCase3 (T : Matrix (Fin k) (Fin n) ℤ) : Prop :=
  ∃ d : Decomp k n, d.IsSumOf T

/-- Case (iv) of Theorem 14. -/
def SeymourCase4 (T : Matrix (Fin k) (Fin n) ℤ) : Prop :=
  ∃ i j, T i j ≠ 0 ∧ ∃ d : Decomp k n, d.kind = 3 ∧ d.IsSumOf (pivot T i j)

/-- A correct output of the decomposition algorithm of Theorem 14: `[1, 0]` (`T` is a network
matrix), `[1, 1]` (`T⊤` is), `[2, 0]` or `[2, 1]` (case (ii) with the first or second matrix),
`3 :: d` (case (iii) with the decomposition `d`), or `[4, i, j] ++ d` (case (iv): pivoting on
`T_ij` gives a matrix with the 3-sum decomposition `d`). -/
def SeymourOut (T : Matrix (Fin k) (Fin n) ℤ) (out : List ℤ) : Prop :=
  (IsNetworkMatrix T ∧ out = [1, 0]) ∨ (IsNetworkMatrix T.transpose ∧ out = [1, 1]) ∨
  (ReducesTo T baseR10 ∧ out = [2, 0]) ∨ (ReducesTo T baseR12 ∧ out = [2, 1]) ∨
  (∃ d : Decomp k n, d.IsSumOf T ∧ out = 3 :: d.enc) ∨
  (∃ i j, T i j ≠ 0 ∧ ∃ d : Decomp k n, d.kind = 3 ∧ d.IsSumOf (pivot T i j) ∧
    out = [4, (i.val : ℤ), (j.val : ℤ)] ++ d.enc)

end CongruencyTU


