-- Prove2me | Definitions.Def_CongruencyTU_Core
-- name    : CongruencyTU_Core
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:44:00.825108+00:00
-- url     : https://prove2.me/theorems/d9f13cea-50a1-4e12-b5ad-8194b4537e80
-- title:
--   Deletion of redundant rows and columns; the core of a TU matrix
-- statement:
--   Two operations delete a row or column of a matrix:
--
--   1. a row or column with at most one non-zero entry;
--   2. a row or column that appears twice, or whose negation also appears in the matrix.
--
--   A **core** of a totally unimodular matrix $T$ is a submatrix obtained from $T$ by iterating these deletions until none applies (a smallest possible such submatrix). $T$ **has a core of size at most $s$** if some core has at most $s$ rows and at most $s$ columns.
--
--   These operations define case (ii) of Seymour's decomposition (Theorem 14) and the class of matrices handled by Theorem 52.
--
--   **Formalization Note** A submatrix is a pair of index sets; the conditions are evaluated inside the current submatrix. Reading "smallest possible" as a minimum size instead gives the same notion of having a core of size at most $s$.
-- source:
--   Nägele, Santiago, Zenklusen, Congruency-Constrained TU Problems Beyond the Bimodular Case, arXiv:2109.03148v3 [math.OC] (preprint, 25 Apr 2023), https://arxiv.org/abs/2109.03148v3, Theorem 14 (ii), p.8 (PDF p.9); Definition 51, p.34 (PDF p.35)

import Mathlib

namespace CongruencyTU

/-! # Deleting redundant rows and columns; the core of a TU matrix

Nägele–Santiago–Zenklusen, arXiv:2109.03148v3 (preprint). Theorem 14 (ii), p.8 (PDF p.9) and
Definition 51, p.34 (PDF p.35) use the operations of deleting
1. a row or column with at most one non-zero entry, and
2. a row or column that appears twice or whose negation also appears in the matrix.
Definition 51: "A submatrix of `T` is a core of `T` if it is a smallest possible submatrix of `T`
that can be obtained by iteratively deleting (i) any row or column with at most one non-zero entry,
or (ii) any row or column appearing twice or whose negation is also in the matrix."

**Formalization Note.** A submatrix is a pair `(I, J)` of row and column index sets; the conditions
are read inside the current submatrix. "Appearing twice" deletes one of two equal rows (columns), so
the deleted row needs another row `i' ≠ i` of the current submatrix equal to it or to its negation.
A core is a submatrix reachable from `T` to which no further deletion applies. ("Smallest possible"
read as a minimum size instead gives the same notion of "having a core with at most `s` rows and
`s` columns", since every reachable submatrix can be reduced further to one where no deletion
applies, and deletions only shrink.) -/

variable {k n : ℕ}

/-- One deletion step on the submatrix `(I, J)` of `T`. -/
inductive DelStep (T : Matrix (Fin k) (Fin n) ℤ) :
    Finset (Fin k) × Finset (Fin n) → Finset (Fin k) × Finset (Fin n) → Prop
  | rowSparse (I : Finset (Fin k)) (J : Finset (Fin n)) (i : Fin k) (hi : i ∈ I)
      (h : (J.filter fun j => T i j ≠ 0).card ≤ 1) : DelStep T (I, J) (I.erase i, J)
  | colSparse (I : Finset (Fin k)) (J : Finset (Fin n)) (j : Fin n) (hj : j ∈ J)
      (h : (I.filter fun i => T i j ≠ 0).card ≤ 1) : DelStep T (I, J) (I, J.erase j)
  | rowRepeat (I : Finset (Fin k)) (J : Finset (Fin n)) (i i' : Fin k) (hi : i ∈ I) (hi' : i' ∈ I)
      (hne : i' ≠ i) (h : (∀ j ∈ J, T i' j = T i j) ∨ (∀ j ∈ J, T i' j = -T i j)) :
      DelStep T (I, J) (I.erase i, J)
  | colRepeat (I : Finset (Fin k)) (J : Finset (Fin n)) (j j' : Fin n) (hj : j ∈ J) (hj' : j' ∈ J)
      (hne : j' ≠ j) (h : (∀ i ∈ I, T i j' = T i j) ∨ (∀ i ∈ I, T i j' = -T i j)) :
      DelStep T (I, J) (I, J.erase j)

/-- `(I, J)` is obtained from `T` by iterated deletions. -/
def DelReachable (T : Matrix (Fin k) (Fin n) ℤ) (c : Finset (Fin k) × Finset (Fin n)) : Prop :=
  Relation.ReflTransGen (DelStep T) (Finset.univ, Finset.univ) c

/-- **Core** (Definition 51): a submatrix reachable by deletions to which no deletion applies. -/
def IsCore (T : Matrix (Fin k) (Fin n) ℤ) (c : Finset (Fin k) × Finset (Fin n)) : Prop :=
  DelReachable T c ∧ ∀ c', ¬ DelStep T c c'

/-- `T` has a core with at most `s` rows and at most `s` columns. -/
def HasCoreOfSize (T : Matrix (Fin k) (Fin n) ℤ) (s : ℕ) : Prop :=
  ∃ c, IsCore T c ∧ c.1.card ≤ s ∧ c.2.card ≤ s

end CongruencyTU


