-- Prove2me | Definitions.Def_MatrixSpencer_matWeight
-- name    : MatrixSpencer_matWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:44:21.215648+00:00
-- url     : https://prove2.me/theorems/317d33ec-b45f-4bec-b6c9-5811550af4db
-- title:
--   The matrix weight $W(g)=e^{-\|g\|_2^2/2-V(B(g))}(R\otimes R)$
-- statement:
--   With $R=(I-B(g))^{-1}$, the matrix weight of the proof of Lemma 2.6:
--   $$W(g)=e^{-\|g\|_2^2/2-V(B(g))}(R\otimes R),$$
--   a $d^2\times d^2$ matrix, $\otimes$ being the Kronecker product.
-- source:
--   E. Akbas, S. Sra, A Proof of the Matrix Spencer Conjecture, arXiv:2608.28816 (held file sha256 3e56f6a1…), proof of Lemma 2.6, p.27

import Mathlib
import Definitions.Def_MatrixSpencer_series
import Definitions.Def_MatrixSpencer_weight
import Definitions.Def_MatrixSpencer_resolvent
open RBMSensitivity (E)
open scoped Kronecker

namespace MatrixSpencer

/-- **The matrix weight `W(g) = e^{−‖g‖²₂/2 − V(B(g))} (R ⊗ R)`.**
Akbas, Sra, *A Proof of the Matrix Spencer Conjecture*, arXiv:2608.28816 (held file sha256 3e56f6a1…), proof of Lemma 2.6, p.27.

**Formalization Note.** `⊗` is the Kronecker product, a matrix indexed by `Fin d × Fin d`. The
factor `e^{−V(B(g))}` is `weight`. -/
noncomputable def matWeight {n d : ℕ} (α β : ℝ) (p : ℕ) (M : Fin n → Matrix (Fin d) (Fin d) ℝ)
    (g : E n) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℝ :=
  (Real.exp (-(‖g‖ ^ 2) / 2) * weight α β p (series M g)) •
    (resolvent (series M g) ⊗ₖ resolvent (series M g))

end MatrixSpencer


