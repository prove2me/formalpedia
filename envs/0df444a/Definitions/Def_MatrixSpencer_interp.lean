-- Prove2me | Definitions.Def_MatrixSpencer_interp
-- name    : MatrixSpencer_interp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:43:40.567141+00:00
-- url     : https://prove2.me/theorems/09a5aa6c-76f4-473a-9503-77a01b79cd82
-- title:
--   The interpolation $B_t(g)=B_{\mathrm d}(g)+tY(g)$
-- statement:
--   The interpolation between the diagonal and the off-diagonal part of the series:
--   $$B_t(g)=B_{\mathrm d}(g)+tY(g).$$
--   At $t=0$ it is the diagonal part, at $t=1$ it is $B(g)$.
-- source:
--   E. Akbas, S. Sra, A Proof of the Matrix Spencer Conjecture, arXiv:2608.28816 (held file sha256 3e56f6a1…), Theorem 2.5, p.8

import Mathlib
import Definitions.Def_MatrixSpencer_series
import Definitions.Def_MatrixSpencer_diagPart
import Definitions.Def_MatrixSpencer_offSeries
open RBMSensitivity (E)

namespace MatrixSpencer

/-- **The interpolation `B_t(g) = B_d(g) + tY(g)`.**
Akbas, Sra, *A Proof of the Matrix Spencer Conjecture*, arXiv:2608.28816 (held file sha256 3e56f6a1…), Theorem 2.5, p.8. At `t = 1` it is `B(g)`, at `t = 0` the diagonal part. -/
def interp {n d : ℕ} (M : Fin n → Matrix (Fin d) (Fin d) ℝ) (t : ℝ) (g : E n) :
    Matrix (Fin d) (Fin d) ℝ :=
  diagPart (series M g) + t • offSeries M g

end MatrixSpencer


