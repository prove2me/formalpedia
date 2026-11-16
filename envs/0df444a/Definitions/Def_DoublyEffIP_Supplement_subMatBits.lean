-- Prove2me | Definitions.Def_DoublyEffIP_Supplement_subMatBits
-- name    : DoublyEffIP_Supplement_subMatBits
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:34:49.328099+00:00
-- url     : https://prove2.me/theorems/49a5fe9a-dae1-422e-b743-cf203f142d7b
-- title:
--   The row submatrix $M[Q,:]$
-- statement:
--   For a $k\times L$ bit matrix $M$ and a listing $s_0,\dots,s_{m-1}$ of row indices, $M[Q,:]$ is the list of entries of rows $s_0,\dots,s_{m-1}$ of $M$, row by row, in the order of the listing. This is the submatrix "consisting of rows indexed by $Q$".
--
--   **Formalization Note** An index $\ge k$, which a valid description of $Q\subsetneq[k]$ never produces, reads as a row of zeros.
-- source:
--   Chen–Hong–Kalai–Xi, Towards a Doubly Efficient IP = PSPACE, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Section 3, p.8 (A[S, :]); Definition 9, p.12

import Mathlib

set_option autoImplicit false

namespace DoublyEffIP.Supplement

/-- **The row submatrix `M[Q, :]`, row by row** — Chen–Hong–Kalai–Xi, *Towards a Doubly Efficient IP = PSPACE*, arXiv:2606.21799
(version of 2026-11-02, sha256 14d170db…), Section 3, p.8: "For a subset S ⊂ [m],
A[S, :] denotes the submatrix of A consisting of rows indexed by S", used in Definition 9 (p.12).

For a `k × L` bit matrix `M` and a listing `s 0, …, s (m−1)` of row indices, the entries of rows
`s 0, …, s (m−1)` of `M`, row by row.

**Formalization Note.** Rows are listed in the order of the set's description (`DescribesRows`).
An index `≥ k` (never produced by a valid description) reads as a row of zeros. -/
def subMatBits {k L m : ℕ} (M : Fin k → Fin L → Bool) (s : Fin m → ℕ) : List Bool :=
  (List.ofFn fun i : Fin m => List.ofFn fun j : Fin L =>
    if h : s i < k then M ⟨s i, h⟩ j else false).flatten

end DoublyEffIP.Supplement


