-- Prove2me | Definitions.Def_MatrixSpencer_MatInst
-- name    : MatrixSpencer_MatInst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:41:03.221613+00:00
-- url     : https://prove2.me/theorems/ac686ae9-8c92-4354-b123-a0e6257b2c57
-- title:
--   A rational instance of matrix discrepancy
-- statement:
--   An instance consists of natural numbers $n,d$ and matrices $A_1,\dots,A_n\in\mathbb Q^{d\times d}$. It is the input format of the algorithmic clause of the main theorem.
--
--   **Formalization Note** Symmetry and the norm bound are promises in the theorem, not part of the data.
-- source:
--   E. Akbas, S. Sra, A Proof of the Matrix Spencer Conjecture, arXiv:2608.28816 (held file sha256 3e56f6a1…), Theorem 1.3, p.1

import Mathlib

namespace MatrixSpencer

/-- **A rational instance of matrix discrepancy.**
Akbas, Sra, *A Proof of the Matrix Spencer Conjecture*, arXiv:2608.28816 (held file sha256 3e56f6a1…), Theorem 1.3, p.1: "symmetric d × d matrices A₁, …, Aₙ", and "can be found efficiently".

**Formalization Note.** The paper names no machine. An input a Turing machine can read has rational
entries (reading of "efficiently"; see `theorem_1_3`). Symmetry and the norm bound are promises in the
theorem, not part of the data. -/
structure MatInst where
  /-- the number of matrices -/
  n : ℕ
  /-- the dimension -/
  d : ℕ
  /-- the matrices -/
  A : Fin n → Matrix (Fin d) (Fin d) ℚ

end MatrixSpencer


