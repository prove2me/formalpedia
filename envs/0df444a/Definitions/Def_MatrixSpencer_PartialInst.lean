-- Prove2me | Definitions.Def_MatrixSpencer_PartialInst
-- name    : MatrixSpencer_PartialInst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:42:14.467046+00:00
-- url     : https://prove2.me/theorems/c033d609-184a-4eff-8946-8c0cfc8ac558
-- title:
--   A rational instance of partial coloring
-- statement:
--   An instance consists of a matrix instance and a starting point $x^{(0)}\in\mathbb Q^n$.
--
--   **Formalization Note** That $x^{(0)}\in(-1,1)^n$ and that the matrices are symmetric are promises in the theorem. The parameter $\sigma$ is not part of the input.
-- source:
--   E. Akbas, S. Sra, A Proof of the Matrix Spencer Conjecture, arXiv:2608.28816 (held file sha256 3e56f6a1…), Theorem 2.7, p.11

import Mathlib
import Definitions.Def_MatrixSpencer_MatInst

namespace MatrixSpencer

/-- **A rational instance of the partial-coloring problem.**
Akbas, Sra, *A Proof of the Matrix Spencer Conjecture*, arXiv:2608.28816 (held file sha256 3e56f6a1…), Theorem 2.7, p.11: the matrices and the starting point `x⁽⁰⁾`.

**Formalization Note.** That `|xᵢ⁽⁰⁾| < 1` and that the matrices are symmetric are promises in the
theorem. `σ` is not part of the input: the algorithm's guarantee uses the smallest admissible `σ`. -/
structure PartialInst where
  /-- the matrices -/
  inst : MatInst
  /-- the starting point -/
  x0 : Fin inst.n → ℚ

end MatrixSpencer


