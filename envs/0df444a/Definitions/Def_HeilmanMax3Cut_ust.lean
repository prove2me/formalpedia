-- Prove2me | Definitions.Def_HeilmanMax3Cut_ust
-- name    : HeilmanMax3Cut_ust
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:32:35.631777+00:00
-- url     : https://prove2.me/theorems/0e71fe75-ab4e-49e6-9c67-ce7e855f60b9
-- title:
--   $u_*=K_*1$
-- statement:
--   $$u_*(t)=\int_0^\infty K_*(t,s)\,d\nu(s).$$
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Eq. (108), p.31, and p.32

import Mathlib
import Definitions.Def_HeilmanMax3Cut_Kst
import Definitions.Def_HeilmanMax3Cut_nuExp
open MeasureTheory

namespace HeilmanMax3Cut

/-- **`u_* := K_* 1`.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Eq. (108), p.31, and its unfolding on p.32:
`u_*(t) = ∫₀^∞ K_*(t, s) dν(s)`. -/
noncomputable def ust (σ t : ℝ) : ℝ :=
  ∫ s, Kst σ t s ∂nuExp

end HeilmanMax3Cut


