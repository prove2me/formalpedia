-- Prove2me | Definitions.Def_MatrixSpencer_offSeries
-- name    : MatrixSpencer_offSeries
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:42:03.140212+00:00
-- url     : https://prove2.me/theorems/cc5ec685-717d-4668-8246-e67ff5d7ded9
-- title:
--   The off-diagonal part $Y(g)$
-- statement:
--   For $B(g)=\sum_i g_iM_i$ with diagonal part $B_{\mathrm d}(g)=\mathrm{diag}(B(g))$, the off-diagonal part
--   $$Y(g)=B(g)-B_{\mathrm d}(g).$$
-- source:
--   E. Akbas, S. Sra, A Proof of the Matrix Spencer Conjecture, arXiv:2608.28816 (held file sha256 3e56f6a1…), Theorem 2.5, p.8

import Mathlib
import Definitions.Def_MatrixSpencer_series
import Definitions.Def_MatrixSpencer_diagPart
open RBMSensitivity (E)

namespace MatrixSpencer

/-- **The off-diagonal part `Y(g) = B(g) − B_d(g)`.**
Akbas, Sra, *A Proof of the Matrix Spencer Conjecture*, arXiv:2608.28816 (held file sha256 3e56f6a1…), Theorem 2.5, p.8: "B_t(g) = B_d(g) + tY(g) the interpolation between diagonal and off diagonal
part of the matrix series B". -/
def offSeries {n d : ℕ} (M : Fin n → Matrix (Fin d) (Fin d) ℝ) (g : E n) :
    Matrix (Fin d) (Fin d) ℝ :=
  series M g - diagPart (series M g)

end MatrixSpencer


