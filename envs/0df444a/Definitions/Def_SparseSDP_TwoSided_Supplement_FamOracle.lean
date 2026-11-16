-- Prove2me | Definitions.Def_SparseSDP_TwoSided_Supplement_FamOracle
-- name    : SparseSDP_TwoSided_Supplement_FamOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:30:52.494278+00:00
-- url     : https://prove2.me/theorems/ce62c15f-5a28-41eb-92ee-a56c637ea8dc
-- title:
--   Sparse oracle access (Definition 2.1) to an indexed family of complex matrices, and charged row reads
-- statement:
--   Let $(M_\ell)_{\ell\in\iota}$ be a family of complex $n\times n$ matrices. **Sparse oracle access** (Definition 2.1) to the family provides, for each $\ell$:
--
--   1. $O_{\mathrm{sparse}}(M_\ell,i,k)$: the column index of the $k$-th nonzero entry in row $i$ of $M_\ell$, or a null symbol if row $i$ has fewer than $k$ nonzeros;
--   2. $O_{M_\ell}(i,c)$: the entry $[M_\ell]_{i,c}$.
--
--   Each call costs one operation. A row is read by calling $O_{\mathrm{sparse}}$ for $k=1,2,\dots$ until the null symbol, reading each entry; an $s$-row-sparse row costs $O(s)$. A **row reader** for a family is any charged procedure returning rows as lists of (column, value) pairs; the product of such a row with a stored complex vector is charged $8\cdot(\text{length})+1$.
--
--   This is the input model of Theorem 5.1, for the Hamiltonian terms $B_\ell$ and the observables $A_j$.
--
--   **Formalization Note** "The $k$-th nonzero" is read, as in the published `SparseOracle`, as any fixed enumeration of the row's nonzeros without repetition. This module mirrors that structure for an arbitrary indexed family; it does not change `SparseOracle`.
-- source:
--   Brandão, Dalzell, Gilyén, Vasconcelos, Solving Sparse SDPs in Sublinear Time, arXiv:2609.40302, Definition 2.1, p. 15; Theorem 5.1, p. 27

import Mathlib
import Definitions.Def_SparseSDP_TwoSided_Supplement_cvec

open Matrix

namespace SparseSDP.TwoSided.Supplement

open SparseSDP.TwoSided

/-- A row of a complex matrix in sparse form: a list of (column, value) pairs. -/
abbrev CRow (n : ℕ) : Type := List (Fin n × ℂ)

variable {ι : Type} {n : ℕ}

/-- Sparse oracle access (Definition 2.1, p. 15) to every member of an indexed family `M` of complex
`n × n` matrices: `col ℓ i k` is `O_sparse(M_ℓ, i, k)`, the column of the `k`-th nonzero of row `i`
(`k = 1, 2, …`), or `none` if row `i` has fewer than `k` nonzeros.

Brandão, Dalzell, Gilyén, Vasconcelos, *Solving Sparse SDPs in Sublinear Time*, arXiv:2609.40302,
Definition 2.1, p. 15; used for the families `(B_ℓ)` and `(A_j)` of Theorem 5.1, p. 27.

**Formalization Note.** This mirrors the published `SparseSDP.TwoSided.SparseOracle` (same
enumeration field `enum`, read as any fixed enumeration of the nonzeros without repetition) for an
arbitrary indexed family instead of the matrices of an `Instance`. -/
structure FamOracle (M : ι → Matrix (Fin n) (Fin n) ℂ) where
  /-- `O_sparse`. -/
  col : ι → Fin n → ℕ → Option (Fin n)
  /-- `col` enumerates the nonzeros of the row. -/
  enum : ∀ ℓ i, ∃ l : List (Fin n), l.Nodup ∧ (∀ c, c ∈ l ↔ M ℓ i c ≠ 0) ∧
    ∀ k, col ℓ i (k + 1) = l[k]?

variable {M : ι → Matrix (Fin n) (Fin n) ℂ}

/-- One call to `O_sparse`, at unit cost. -/
def qColF (orc : FamOracle M) (ℓ : ι) (i : Fin n) (k : ℕ) : Prog (Option (Fin n)) :=
  op 1 (orc.col ℓ i k)

/-- One call to `O_M`, at unit cost. The entries of `M` are read here and nowhere else. -/
def qEntryF (_orc : FamOracle M) (ℓ : ι) (i c : Fin n) : Prog ℂ := op 1 (M ℓ i c)

/-- Read row `i` of `M_ℓ` by calling `O_sparse` for `k = 1, 2, …` until `none`, reading each entry
(as the published `readRow`). -/
def readRowF (orc : FamOracle M) (ℓ : ι) (i : Fin n) : Prog (CRow n) := do
  let mut out : CRow n := []
  for k in List.range (n + 1) do
    tick 1
    let c ← qColF orc ℓ i (k + 1)
    match c with
    | none => break
    | some cc =>
      let z ← qEntryF orc ℓ i cc
      tick 1
      out := (cc, z) :: out
  pure out

/-- A charged row reader for a family of complex `n × n` matrices indexed by `ι`. Algorithm 5 reads
its Hamiltonian terms and its observables only through such readers. -/
structure CRowAccess (ι : Type) (n : ℕ) where
  /-- Read row `i` of matrix `ℓ`. -/
  read : ι → Fin n → Prog (CRow n)

/-- The row reader of a family given by sparse oracle access. -/
def famAccess (orc : FamOracle M) : CRowAccess ι n := ⟨readRowF orc⟩

/-- The product of a sparse row with a stored complex vector, `∑ₚ value · x_column`, charged
`8 · length + 1`. -/
noncomputable def crowDot (row : CRow n) (x : CVec n) : Prog ℂ :=
  op (8 * row.length + 1) (row.map fun p => p.2 * x p.1).sum

end SparseSDP.TwoSided.Supplement


