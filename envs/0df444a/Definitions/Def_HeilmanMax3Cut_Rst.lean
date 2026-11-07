-- Prove2me | Definitions.Def_HeilmanMax3Cut_Rst
-- name    : HeilmanMax3Cut_Rst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:35:30.132382+00:00
-- url     : https://prove2.me/theorems/f8bce17b-6f51-4b97-9957-404ae1a1c1a4
-- title:
--   The residual kernel $R_*$
-- statement:
--   For $t,s>0$,
--
--   $$R_*(t,s)=K_*(t,s)-\frac{u_*(t)\,u_*(s)}{C_*}.$$
--
--   $R_*$ has zero row and column integrals.
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Eq. (109), p.31

import Mathlib
import Definitions.Def_HeilmanMax3Cut_Kst
import Definitions.Def_HeilmanMax3Cut_ust
import Definitions.Def_HeilmanMax3Cut_Cst

namespace HeilmanMax3Cut

/-- **The residual kernel `R_*`.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Eq. (109), p.31:
`R_*(t, s) := K_*(t, s) − u_*(t) u_*(s) / C_*`, `t, s > 0`.

**Formalization Note.** `C_* > 0` (p.32), so the division is genuine. -/
noncomputable def Rst (σ t s : ℝ) : ℝ :=
  Kst σ t s - ust σ t * ust σ s / Cst σ

end HeilmanMax3Cut


