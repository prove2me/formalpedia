-- Prove2me | Definitions.Def_MatrixSpencer_pdV
-- name    : MatrixSpencer_pdV
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:41:16.75623+00:00
-- url     : https://prove2.me/theorems/64f3465d-5cbd-4264-9f85-8e303593cf4c
-- title:
--   The entrywise partial derivative $\partial_iF$
-- statement:
--   For a vector field $F$ on $\mathbb R^n$, the vector $\partial_iF(x)$ of the partial derivatives of its coordinates in the direction of the $i$th standard basis vector.
-- source:
--   E. Akbas, S. Sra, A Proof of the Matrix Spencer Conjecture, arXiv:2608.28816 (held file sha256 3e56f6a1…), Lemma 2.1, p.7

import Mathlib
import Definitions.Def_RBMSensitivity_E
open RBMSensitivity (E)

namespace MatrixSpencer

/-- **The entrywise partial derivative `∂ᵢF` of a vector field.**
Akbas, Sra, *A Proof of the Matrix Spencer Conjecture*, arXiv:2608.28816 (held file sha256 3e56f6a1…), Lemma 2.1, p.7.

**Formalization Note.** As in `pdM`. The field `F` is `C¹` on the open set where it is read. -/
noncomputable def pdV {n : ℕ} {ι : Type} (i : Fin n) (F : E n → ι → ℝ) (x : E n) : ι → ℝ :=
  fun a => fderiv ℝ (fun y => F y a) x (EuclideanSpace.single i 1)

end MatrixSpencer


