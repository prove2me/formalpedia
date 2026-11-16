-- Prove2me | Definitions.Def_MatMulDS_Supplement_minWitness
-- name    : MatMulDS_Supplement_minWitness
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T20:14:00.556696+00:00
-- url     : https://prove2.me/theorems/e7ccaa9b-bef1-4550-bd5b-1cee1290d420
-- title:
--   The minimum witness product
-- statement:
--   For Boolean matrices $A\in\{0,1\}^{a\times b}$ and $B\in\{0,1\}^{b\times c}$, an index $k\in[b]$ with $A_{ik}=B_{kj}=1$ is a **witness** of $(i,j)$ (footnote 12). The **minimum witness product** of $A$ and $B$ is the matrix with entries
--   $$\min\{k\in[b]:A_{ik}=B_{kj}=1\},$$
--   where $\min\emptyset=\infty$ (footnote 13). It is the output of Theorems 8.5 and C.1.
--
--   **Formalization Note** Indices are $0$-based, and $\infty$ is $\top$ in `WithTop (Fin b)`, coded $-1$ in a word. Dense input: $n$, then $A$ and $B$ in row-major order as $0/1$.
-- source:
--   J. Alman, J. Nogler, V. Vassilevska Williams, Subquadratic Time Matrix Multiplication Data Structures Beyond the Dual Exponent, with Applications, STOC 2027 submission (held file sha256 6c5a1c16…), footnotes 12, 13, p.53 (PDF p.55)

import Mathlib

set_option autoImplicit false

namespace MatMulDS.Supplement

/-- The witnesses of `(i, j)` (footnote 12, p.53): the indices `k` with `A_ik = B_kj = 1`. -/
def witnesses {a b c : ℕ} (A : Matrix (Fin a) (Fin b) Bool) (B : Matrix (Fin b) (Fin c) Bool) (i : Fin a) (j : Fin c) :
    Finset (Fin b) :=
  Finset.univ.filter fun k => A i k = true ∧ B k j = true

/-- **The minimum witness product** (footnote 13, p.53, PDF p.55; Alman, Nogler, Vassilevska Williams, STOC 2027
submission, held file sha256 6c5a1c16…): the matrix with entries `min {k ∈ [b] : A_ik = B_kj = 1}`, where `min ∅ = ∞`,
here `⊤`.

**Formalization Note** Indices are 0-based, so the entry is the source's minimum witness minus one. -/
def minWitness {a b c : ℕ} (A : Matrix (Fin a) (Fin b) Bool) (B : Matrix (Fin b) (Fin c) Bool) (i : Fin a) (j : Fin c) :
    WithTop (Fin b) :=
  (witnesses A B i j).min

/-- The word code of an entry of the minimum witness product: the witness `k` (0-based), or `−1` for `∞`. -/
def witnessCode {b : ℕ} : WithTop (Fin b) → ℤ
  | ⊤ => -1
  | (k : Fin b) => ((k : ℕ) : ℤ)

/-- The input words of two dense `n × n` Boolean matrices: `n`, then `A` and `B` in row-major order, as `0`/`1`. -/
def boolWords {n : ℕ} (A B : Matrix (Fin n) (Fin n) Bool) : List ℤ :=
  (n : ℤ) :: ((List.finRange n).flatMap fun i => (List.finRange n).map fun j => if A i j then (1 : ℤ) else 0) ++
    ((List.finRange n).flatMap fun i => (List.finRange n).map fun j => if B i j then (1 : ℤ) else 0)

end MatMulDS.Supplement


