-- Prove2me | Definitions.Def_MatrixSpencer_vPot
-- name    : MatrixSpencer_vPot
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:41:52.875706+00:00
-- url     : https://prove2.me/theorems/248b5acd-c9b6-48cb-acd8-6640f179c0b7
-- title:
--   The spectral potential $v=\beta\ell+(\alpha-\beta)r_p$
-- statement:
--   For real $\alpha,\beta$ and an integer $p$, the scalar potential
--   $$v(x)=\beta\ell(x)+(\alpha-\beta)r_p(x),\qquad |x|<1.$$
-- source:
--   E. Akbas, S. Sra, A Proof of the Matrix Spencer Conjecture, arXiv:2608.28816 (held file sha256 3e56f6a1…), §2.2, p.8

import Mathlib
import Definitions.Def_MatrixSpencer_ell
import Definitions.Def_MatrixSpencer_tailR

namespace MatrixSpencer

/-- **The spectral potential `v(x) = βℓ(x) + (α − β)r_p(x)`.**
Akbas, Sra, *A Proof of the Matrix Spencer Conjecture*, arXiv:2608.28816 (held file sha256 3e56f6a1…), §2.2, p.8. -/
noncomputable def vPot (α β : ℝ) (p : ℕ) (x : ℝ) : ℝ :=
  β * ell x + (α - β) * tailR p x

end MatrixSpencer


