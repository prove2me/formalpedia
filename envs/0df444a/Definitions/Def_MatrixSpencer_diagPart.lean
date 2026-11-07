-- Prove2me | Definitions.Def_MatrixSpencer_diagPart
-- name    : MatrixSpencer_diagPart
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:41:02.211447+00:00
-- url     : https://prove2.me/theorems/5032466b-3db8-41a5-9784-26a21cb35105
-- title:
--   The diagonal part $\mathrm{diag}(A)$
-- statement:
--   The diagonal matrix $\mathrm{diag}(A)$ obtained from a square matrix $A$ by setting the off-diagonal entries to zero, in the standard basis.
-- source:
--   E. Akbas, S. Sra, A Proof of the Matrix Spencer Conjecture, arXiv:2608.28816 (held file sha256 3e56f6a1…), §2.1, p.6

import Mathlib

namespace MatrixSpencer

/-- **The diagonal part `diag(A)`.**
Akbas, Sra, *A Proof of the Matrix Spencer Conjecture*, arXiv:2608.28816 (held file sha256 3e56f6a1…), §2.1, p.6: "We write diag(A) for the diagonal matrix obtained by setting the off-diagonal entries
of A to zero." -/
def diagPart {d : ℕ} (X : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.diagonal fun a => X a a

end MatrixSpencer


