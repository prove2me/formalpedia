-- Prove2me | Definitions.Def_HeilmanMax3Cut_Cst
-- name    : HeilmanMax3Cut_Cst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:33:50.330944+00:00
-- url     : https://prove2.me/theorems/1b51a96f-e88b-4065-bc5f-402c30208470
-- title:
--   $C_*=\langle1,u_*\rangle$
-- statement:
--   $$C_*=\int_0^\infty u_*(t)\,d\nu(t)=\int_0^\infty\!\!\int_0^\infty K_*(t,s)\,d\nu(s)\,d\nu(t).$$
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Eq. (108), p.31

import Mathlib
import Definitions.Def_HeilmanMax3Cut_ust
import Definitions.Def_HeilmanMax3Cut_nuExp
open MeasureTheory

namespace HeilmanMax3Cut

/-- **`C_* := ⟨1, u_*⟩`.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Eq. (108), p.31: `C_* = ∫₀^∞ u_*(t) dν(t)`. -/
noncomputable def Cst (σ : ℝ) : ℝ :=
  ∫ t, ust σ t ∂nuExp

end HeilmanMax3Cut


