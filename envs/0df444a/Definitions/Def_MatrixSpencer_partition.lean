-- Prove2me | Definitions.Def_MatrixSpencer_partition
-- name    : MatrixSpencer_partition
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:44:54.620481+00:00
-- url     : https://prove2.me/theorems/7323afda-77d4-4607-b71e-989eb25954f1
-- title:
--   The partition function $Z_t$
-- statement:
--   The partition function associated with the potential $V$:
--   $$Z_t=\mathbb E_{\gamma_n}e^{-V(B_t)}.$$
-- source:
--   E. Akbas, S. Sra, A Proof of the Matrix Spencer Conjecture, arXiv:2608.28816 (held file sha256 3e56f6a1…), Theorem 2.5, p.8

import Mathlib
import Definitions.Def_MatrixSpencer_gam
import Definitions.Def_MatrixSpencer_weight
import Definitions.Def_MatrixSpencer_interp

namespace MatrixSpencer

/-- **The partition function `Z_t = E_{γₙ} e^{−V(B_t)}`.**
Akbas, Sra, *A Proof of the Matrix Spencer Conjecture*, arXiv:2608.28816 (held file sha256 3e56f6a1…), Theorem 2.5, p.8.

**Formalization Note.** `weight` is the bounded function `e^{−V}`, zero outside the unit ball. -/
noncomputable def partition {n d : ℕ} (α β : ℝ) (p : ℕ) (M : Fin n → Matrix (Fin d) (Fin d) ℝ)
    (t : ℝ) : ℝ :=
  ∫ g, weight α β p (interp M t g) ∂(gam n)

end MatrixSpencer


