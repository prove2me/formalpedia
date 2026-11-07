-- Prove2me | Definitions.Def_HeilmanMax3Cut_mulForm
-- name    : HeilmanMax3Cut_mulForm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:28:13.295212+00:00
-- url     : https://prove2.me/theorems/a410e2eb-9cf4-4a86-9921-53c63d24e586
-- title:
--   The form $\langle x,M_Jx\rangle$ on $L^2(\nu)$
-- statement:
--   For a multiplier $J$ and a function $x$ on $(0,\infty)$,
--
--   $$\langle x,M_Jx\rangle=\int_0^\infty J(t)\,x(t)^2\,d\nu(t).$$
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), (105), p.31

import Mathlib
import Definitions.Def_HeilmanMax3Cut_nuExp
open MeasureTheory

namespace HeilmanMax3Cut

/-- **The form `⟨x, M_J x⟩` on `L²(ν)`.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), (105), p.31: `M_J` is multiplication by `J`, so
`⟨x, M_J x⟩ = ∫₀^∞ J(t) x(t)² dν(t)`. -/
noncomputable def mulForm (J x : ℝ → ℝ) : ℝ :=
  ∫ t, J t * x t ^ 2 ∂nuExp

end HeilmanMax3Cut


