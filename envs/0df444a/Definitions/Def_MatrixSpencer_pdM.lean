-- Prove2me | Definitions.Def_MatrixSpencer_pdM
-- name    : MatrixSpencer_pdM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:41:18.859747+00:00
-- url     : https://prove2.me/theorems/a98af760-5c26-4517-af1d-e28495eee1d3
-- title:
--   The entrywise partial derivative $\partial_iW$
-- statement:
--   For a matrix-valued function $W$ on $\mathbb R^n$, the matrix $\partial_iW(x)$ of the partial derivatives of its entries in the direction of the $i$th standard basis vector.
--
--   **Formalization Note** It is the Fréchet derivative applied to the basis vector; the statements read it only where the entries are smooth.
-- source:
--   E. Akbas, S. Sra, A Proof of the Matrix Spencer Conjecture, arXiv:2608.28816 (held file sha256 3e56f6a1…), Lemma 2.1, p.7

import Mathlib
import Definitions.Def_RBMSensitivity_E
open RBMSensitivity (E)

namespace MatrixSpencer

/-- **The entrywise partial derivative `∂ᵢW` of a matrix function.**
Akbas, Sra, *A Proof of the Matrix Spencer Conjecture*, arXiv:2608.28816 (held file sha256 3e56f6a1…), Lemma 2.1, p.7.

**Formalization Note.** `∂ᵢ` is the Fréchet derivative in the direction of the `i`th standard basis
vector, taken entry by entry. Statements using it hold on an open set where the entries are smooth,
so Lean's junk derivative is not read. -/
noncomputable def pdM {n : ℕ} {ι : Type} (i : Fin n) (W : E n → Matrix ι ι ℝ) (x : E n) :
    Matrix ι ι ℝ :=
  Matrix.of fun a b => fderiv ℝ (fun y => W y a b) x (EuclideanSpace.single i 1)

end MatrixSpencer


