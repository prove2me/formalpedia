-- Prove2me | Definitions.Def_TrDegJac_Supplement_IsNonRigid
-- name    : TrDegJac_Supplement_IsNonRigid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:32:40.290003+00:00
-- url     : https://prove2.me/theorems/2497b68a-1b35-4cae-b452-adad64b7f067
-- title:
--   Non-rigid matrices (sum of a rank-$\le r$ and an $s$-sparse matrix)
-- statement:
--   Let $\mathbb F$ be a field and let $r,s$ be real numbers. A matrix $M$ with entries in $\mathbb F$ is **not $(r,s)$-rigid** if it can be written as
--   $$
--   M = L + S,\qquad \operatorname{rank}_{\mathbb F} L \le r,\qquad \#\{(i,j) : S_{ij}\neq 0\}\le s,
--   $$
--   that is, as the sum of a matrix of rank at most $r$ and a matrix with at most $s$ non-zero entries. A matrix is **$(r,s)$-rigid** if no such decomposition exists.
--
--   Rigid matrices are the objects of Valiant's approach to lower bounds for linear circuits; equations vanishing on all non-rigid matrices (Theorem 3.41) certify rigidity of any matrix on which they do not vanish.
--
--   **Formalization Note** The bounds $r$ and $s$ are real numbers and both comparisons are made in $\mathbb R$ (equivalently with $\lfloor r\rfloor$, $\lfloor s\rfloor$), since Theorem 3.41 uses $r=\epsilon n$ and $s=\epsilon n^2$. Rank is `Matrix.rank` over $\mathbb F$; the count of non-zero entries is the `Set.ncard` of the finite set of index pairs where $S$ is non-zero. $L$ and $S$ may have overlapping supports. Rows and columns are indexed by arbitrary finite types; the paper's $n\times n$ matrices are the case `Fin n`, `Fin n`.
-- source:
--   Forbes and Staicu, Approximating Transcendence Degree in Medium Characteristic, STOC 2027 submission (manuscript sha256 3ab72a42c5143c0b6b5eb0d6c9e7be9b837e30a44865fdefd2ea6a908192e92b), §1.2, p.5 ("A matrix is not (r, s)-rigid if …") and §3.3, p.22

import Mathlib

set_option autoImplicit false

namespace TrDegJac.Supplement

/-- **Non-rigid matrices** — Forbes and Staicu, *Approximating Transcendence Degree in Medium
Characteristic*, STOC 2027 submission (manuscript sha256 3ab72a42…), §1.2, p.5: "A matrix is not
(r, s)-rigid if it is the sum of a matrix of rank at most r and a matrix with at most s non-zero
entries"; §3.3, p.22: "a matrix is (r, s)-rigid if it cannot be expressed as the sum of a rank-r
matrix, and an s-sparse matrix."

`IsNonRigid r s M` says that `M = L + S` for some matrices `L`, `S` over the same field, with
`rank L ≤ r` and at most `s` non-zero entries in `S`.

**Formalization Note.** The bounds `r`, `s` are real numbers (Theorem 3.41 uses `r = εn`,
`s = εn²`), and both comparisons are made in `ℝ`; this is the same as comparing with `⌊r⌋`, `⌊s⌋`.
Rank is `Matrix.rank` over the field `F`. The number of non-zero entries of `S` is the cardinality
(`Set.ncard`) of the finite set of index pairs `(i, j)` with `S i j ≠ 0`. `L` and `S` need not have
disjoint supports. Rows and columns may be indexed by any finite types; the paper's square
`n × n` matrices are the case `Fin n`, `Fin n`. -/
def IsNonRigid {F : Type*} [Field F] {ι κ : Type*} [Fintype ι] [Fintype κ] (r s : ℝ)
    (M : Matrix ι κ F) : Prop :=
  ∃ L S : Matrix ι κ F, M = L + S ∧ (L.rank : ℝ) ≤ r ∧
    (({ij : ι × κ | S ij.1 ij.2 ≠ 0}.ncard : ℕ) : ℝ) ≤ s

end TrDegJac.Supplement


