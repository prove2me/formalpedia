-- Prove2me | Definitions.Def_PQNormIPM1352_Main_Sparse
-- name    : PQNormIPM1352_Main_Sparse
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:06:05.238299+00:00
-- url     : https://prove2.me/theorems/f000b779-46d0-4af2-8d02-432a9452842b
-- title:
--   Sparse non-negative matrices and sparsity patterns
-- statement:
--   The input of the algorithm is a non-negative matrix $A \in \mathbb R^{m\times n}$ in **sparse representation**: the list of its $s$ non-zero entries $(i, j, A(i,j))$ with $0 \le i < m$, $0 \le j < n$, $A(i,j) > 0$ and pairwise distinct positions $(i,j)$. Every position not listed holds $0$, so the matrix is non-negative. The number $s$ of listed entries is the sparsity parameter of all running times.
--
--   For the analysis, a **sparsity pattern** with $s$ entries in an $m\times n$ matrix assigns to each entry number $k \in \{0,\dots,s-1\}$ a row $\mathrm{row}(k)$ and a column $\mathrm{col}(k)$, with distinct entries at distinct positions. The set $S = \{(\mathrm{row}(k), \mathrm{col}(k))\}$ is the support of $A$, and $k$ plays the role of the index $k_{i,j}$ of the paper. A pattern with values $a \in \mathbb R^s$ denotes the matrix with $A(\mathrm{row}(k), \mathrm{col}(k)) = a_k$ and zeros elsewhere. The pattern is **preprocessed** when every row and every column carries at least one entry (no all-zero row or column, as after Step 2 of Algorithm 1); then $\max(m,n) \le s$. The row and column degrees are $d_i = |\{k : \mathrm{row}(k) = i\}|$ and $e_j = |\{k : \mathrm{col}(k) = j\}|$.
--
--   **Formalization Note** Indices are $0$-based. The order of the entries is arbitrary: the lexicographic numbering $k_{i,j}$ of the paper is one admissible choice, and no statement depends on it.
-- source:
--   Marco Pirazzini, Daniel Spielman, A Fast and Accurate Algorithm for the p → q Norm of Sparse Non-Negative Matrices, STOC 2027 submission #1352 (October 2026), §3, p. 7 (sparse representation, support S, s = |S|, removal of all-zero rows and columns, k_{i,j}); Algorithm 1, Step 5, p. 9 (degrees)

import Mathlib

/-!
# Sparse non-negative matrices

Pirazzini–Spielman, STOC 2027 submission #1352, §3, p. 7: "we always assume we are working with
sparse representations of matrices"; `S` is the set of non-zero entries, `s = |S|`, and all-zero
rows and columns are removed in preprocessing.
-/

namespace PQNormIPM1352.Main

/-- The input of Algorithm 1 in sparse representation: dimensions `m, n` and the list of the
non-zero entries `(i, j, A(i,j))`, with `i < m`, `j < n`, `A(i,j) > 0` and pairwise distinct
positions `(i, j)`. Indices are 0-based. The matrix is non-negative because every listed entry is
positive and every unlisted entry is `0`. -/
structure SparseInput where
  m : ℕ
  n : ℕ
  entries : List (ℕ × ℕ × ℝ)
  row_lt : ∀ e ∈ entries, e.1 < m
  col_lt : ∀ e ∈ entries, e.2.1 < n
  pos : ∀ e ∈ entries, 0 < e.2.2
  nodup : (entries.map fun e => (e.1, e.2.1)).Nodup

namespace SparseInput

/-- The number `s` of non-zero entries. -/
def s (A : SparseInput) : ℕ := A.entries.length

/-- The dense `m × n` matrix denoted by the sparse input: `A(i,j)` is the listed value at `(i,j)`
and `0` if `(i,j)` is not listed. -/
noncomputable def toMatrix (A : SparseInput) : Matrix (Fin A.m) (Fin A.n) ℝ :=
  fun i j => ((A.entries.filter fun e => e.1 = (i : ℕ) ∧ e.2.1 = (j : ℕ)).map fun e => e.2.2).sum

end SparseInput

/-- A sparsity pattern with `s` entries in an `m × n` matrix: entry number `k` (`0 ≤ k < s`) sits
at row `row k` and column `col k`, and distinct entries sit at distinct positions. The set
`S = {(row k, col k)}` is the support of §3, p. 7, and `k` plays the role of the index `k_{i,j}`. -/
structure SparsePattern (m n s : ℕ) where
  row : Fin s → Fin m
  col : Fin s → Fin n
  inj : Function.Injective fun k => (row k, col k)

namespace SparsePattern

variable {m n s : ℕ}

/-- The pattern after the preprocessing of §3, p. 7 (Step 2 of Algorithm 1): no all-zero row and
no all-zero column, i.e. every row and every column carries at least one entry. -/
def Preprocessed (P : SparsePattern m n s) : Prop :=
  Function.Surjective P.row ∧ Function.Surjective P.col

/-- The dense matrix with pattern `P` and entry values `a`: `A(i,j) = a k` if `(i,j) = (row k,
col k)`, and `0` otherwise. -/
def toMatrix (P : SparsePattern m n s) (a : Fin s → ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  fun i j => ∑ k, if P.row k = i ∧ P.col k = j then a k else 0

/-- The row degree `d_i = |{j : (i,j) ∈ S}|` (Algorithm 1, Step 5). -/
def rowDeg (P : SparsePattern m n s) (i : Fin m) : ℕ := (Finset.univ.filter fun k => P.row k = i).card

/-- The column degree `e_j = |{i : (i,j) ∈ S}|` (Algorithm 1, Step 5). -/
def colDeg (P : SparsePattern m n s) (j : Fin n) : ℕ := (Finset.univ.filter fun k => P.col k = j).card

/-- The row labels as a function on `ℕ` (the array `k ↦ row k` handed to the programs of the cost
model; `0` beyond `s`). -/
def rowFn (P : SparsePattern m n s) (k : ℕ) : ℕ := if h : k < s then (P.row ⟨k, h⟩ : ℕ) else 0

/-- The column labels as a function on `ℕ` (`0` beyond `s`). -/
def colFn (P : SparsePattern m n s) (k : ℕ) : ℕ := if h : k < s then (P.col ⟨k, h⟩ : ℕ) else 0

end SparsePattern

end PQNormIPM1352.Main


