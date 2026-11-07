-- Prove2me | Definitions.Def_LowErrExt_dimSet
-- name    : LowErrExt_dimSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:52:33.507193+00:00
-- url     : https://prove2.me/theorems/a0bd850d-b3c3-4604-b6e8-96346b99221a
-- title:
--   Dimension of a set of vectors over $\mathbb F_2$
-- statement:
--   The **dimension** of a set $X\subseteq\mathbb F_2^n$ is the dimension of its affine span, i.e. of the linear span of the differences $x-x'$ ($x,x'\in X$).
--
--   **Formalization Note** The empty set gets dimension $0$; it never occurs.
-- source:
--   D. Doron, J. Goodman, Low-Error Extractors, STOC 2027 submission (manuscript sha256 43c922d6…), p.22

import Mathlib

namespace LowErrExt

/-- **Dimension of a set of vectors over `𝔽₂`.**
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…), p.22:
"Given a set X ⊆ Fn2, its dimension is the dimension of its affine span."

**Formalization Note.** The dimension of the affine span of `S` is the dimension of the direction
`vectorSpan 𝔽₂ S`. The empty set gets `0` (the paper never takes the dimension of `∅`). -/
noncomputable def dimSet {n : ℕ} (S : Set (Fin n → ZMod 2)) : ℕ :=
  Module.finrank (ZMod 2) (vectorSpan (ZMod 2) S)

end LowErrExt


