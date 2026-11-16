-- Prove2me | Definitions.Def_MatMulDS_Supplement_sparseWords
-- name    : MatMulDS_Supplement_sparseWords
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T20:13:26.917203+00:00
-- url     : https://prove2.me/theorems/9607326f-db6e-47b1-b01c-ea8cb37a04b6
-- title:
--   Sparse representation of nonnegative integer matrices on the word RAM
-- statement:
--   A matrix is in **sparse representation** if it is given as the list of its nonzero entries with their positions (footnote 10); $\mathrm{nnz}(A)$ is the number of nonzero entries.
--
--   For matrices $A\in\mathbb Z_{\ge0}^{a\times b}$, $B\in\mathbb Z_{\ge0}^{b\times c}$ the input words are $a,b,c$, then $\mathrm{nnz}(A)$ and the triples $(i,j,A_{ij})$ of its nonzero entries in any order, then the same for $B$. A word memory holds a matrix $M$ in sparse representation if cell $0$ holds $\mathrm{nnz}(M)$ and the following cells hold the triples $(i,j,M_{ij})$ of all nonzero entries, each once, in any order. This is the input and output format of Theorem 8.4.
-- source:
--   J. Alman, J. Nogler, V. Vassilevska Williams, Subquadratic Time Matrix Multiplication Data Structures Beyond the Dual Exponent, with Applications, STOC 2027 submission (held file sha256 6c5a1c16…), footnote 10, p.51 (PDF p.53); Theorem 8.4, p.53 (PDF p.55)

import Mathlib
import Definitions.Def_MatMulDS_Supplement_AdmissibleSaving

set_option autoImplicit false

namespace MatMulDS.Supplement

/-- `nnz(M)`, the number of nonzero entries of `M` (footnote 10, p.51). -/
noncomputable def nnz {R : Type} [Zero R] {a b : ℕ} (M : Matrix (Fin a) (Fin b) R) : ℕ :=
  open Classical in (Finset.univ.filter fun p : Fin a × Fin b => M p.1 p.2 ≠ 0).card

/-- The triples `(i, j, M[i, j])` of the positions in `es`, as words, 0-based. -/
def tripleWords {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℕ) (es : List (Fin a × Fin b)) : List ℤ :=
  es.flatMap fun e => [((e.1 : ℕ) : ℤ), ((e.2 : ℕ) : ℤ), ((M e.1 e.2 : ℕ) : ℤ)]

/-- **The input words of two matrices in sparse representation** (footnote 10, p.51): the dimensions `a, b, c`, then the number
of nonzero entries of `A` and their triples, in the order of `esA`, then the same for `B`. -/
def sparseWords {a b c : ℕ} (A : Matrix (Fin a) (Fin b) ℕ) (B : Matrix (Fin b) (Fin c) ℕ)
    (esA : List (Fin a × Fin b)) (esB : List (Fin b × Fin c)) : List ℤ :=
  [(a : ℤ), (b : ℤ), (c : ℤ), (esA.length : ℤ)] ++ tripleWords A esA ++ (esB.length : ℤ) :: tripleWords B esB

/-- The word memory holds `M` **in sparse representation**: word cell `0` holds the number of nonzero entries, and the cells
`1 + 3t, 2 + 3t, 3 + 3t` hold the triple `(i, j, M[i, j])` of the `t`-th of them, each nonzero entry listed once, in any order. -/
def SparseOut {a c w : ℕ} (M : Matrix (Fin a) (Fin c) ℕ) (st : ℤ → BitVec w) : Prop :=
  ∃ es : List (Fin a × Fin c), IsSparseRep M es ∧ (st 0).toInt = es.length ∧
    ∀ (t : ℕ) (ht : t < es.length),
      (st (1 + 3 * t)).toInt = ((es[t].1 : ℕ) : ℤ) ∧ (st (2 + 3 * t)).toInt = ((es[t].2 : ℕ) : ℤ) ∧
      (st (3 + 3 * t)).toInt = ((M es[t].1 es[t].2 : ℕ) : ℤ)

end MatMulDS.Supplement


