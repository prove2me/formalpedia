-- Prove2me | Definitions.Def_MunkresAlg_Assignment_Basic
-- name    : MunkresAlg_Assignment_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T12:53:20.655871+00:00
-- url     : https://prove2.me/theorems/cf07bf2d-1312-4cdd-a021-519341b3a96a
-- title:
--   §1, pp. 32–35 — independent elements, lines containing all the zeros, and the maximal number of independent zeros
-- statement:
--   This module fixes the matrix-level vocabulary of §1 of Munkres' paper. Throughout, $B=(b_{ij})$ is a real $n\times n$ matrix, and a **position** is a pair $(i,j)$ of a row index $i$ and a column index $j$, both in $\{0,\dots,n-1\}$. The word **line** refers both to the rows and to the columns of the matrix.
--
--   1. **Independent positions** (p. 32). A set $S$ of positions is *independent* if no two of its elements lie in the same line: for distinct $p,q\in S$ the rows of $p$ and $q$ differ and the columns of $p$ and $q$ differ.
--   2. **Independent zeros.** $S$ is a set of independent zeros of $B$ if $S$ is independent and $b_{ij}=0$ for every $(i,j)\in S$.
--   3. **Lines containing all the zeros** (p. 34). A set $R$ of rows together with a set $C$ of columns *contains all the zeros* of $B$ if every zero entry $b_{ij}=0$ has $i\in R$ or $j\in C$. The number of lines is $|R|+|C|$.
--   4. **The maximal number of independent zeros** (p. 35, the paper's $n_k$ for the matrix $A_k$):
--   $$
--   \nu(B)=\max\{\,|S| \;:\; S \text{ is a set of independent zeros of } B\,\}.
--   $$
--   The maximum is over a finite family that always contains the empty set, so $\nu(B)$ is a well-defined natural number with $0\le\nu(B)\le n$.
--
--   These notions are the language in which the paper states its invariants: the starred zeros of the algorithm are a set of independent zeros, the covered lines contain all the zeros at Step 3, and termination is measured by the growth of $\nu$.
--
--   **Formalization Note** Positions are elements of `Fin n × Fin n` (row, column). The maximum $\nu(B)$ is a `Finset.sup` of cardinalities over the finite family of independent zero sets, so it carries no junk value.
-- source:
--   Munkres, Algorithms for the assignment and transportation problems, J. SIAM 5 (1957), p. 32 (§1, independent elements), p. 34 (§1, Step 3, first bracket), p. 35 (n_i)

import Mathlib

namespace MunkresAlg.Assignment

open Classical

/-- Munkres (1957), §1, p. 32: a set of positions of an `n × n` matrix is *independent* if no two
of them lie in the same line (row or column). Positions are pairs `(row, column)`. -/
def Independent {n : ℕ} (S : Finset (Fin n × Fin n)) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, p ≠ q → p.1 ≠ q.1 ∧ p.2 ≠ q.2

/-- `S` is a set of independent zeros of the matrix `B`. -/
def IsIndepZeros {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n × Fin n)) : Prop :=
  Independent S ∧ ∀ p ∈ S, B p.1 p.2 = 0

/-- The rows `R` and columns `C` form a set of lines containing all the zeros of `B`
(p. 34, Step 3). The number of lines is `R.card + C.card`. -/
def CoversZeros {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (R C : Finset (Fin n)) : Prop :=
  ∀ i j, B i j = 0 → i ∈ R ∨ j ∈ C

/-- The maximal number of independent zeros of `B` (the paper's `n_k`, p. 35): the largest
cardinality of a set of independent zeros. The family contains `∅`, so the supremum is over a
finite nonempty family of natural numbers. -/
noncomputable def maxIndepZeros {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) : ℕ :=
  ((Finset.univ : Finset (Fin n × Fin n)).powerset.filter (IsIndepZeros B)).sup Finset.card

end MunkresAlg.Assignment


