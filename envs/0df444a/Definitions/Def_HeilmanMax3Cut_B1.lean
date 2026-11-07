-- Prove2me | Definitions.Def_HeilmanMax3Cut_B1
-- name    : HeilmanMax3Cut_B1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:30:55.770923+00:00
-- url     : https://prove2.me/theorems/26889f4d-f79a-4f9c-84c2-9c67ad02598e
-- title:
--   The correction multiplier $B^{(1)}(t)$
-- statement:
--   $$B^{(1)}(t)=\int_0^\infty B(t,s)\,d\nu(s).$$
--
--   **Formalization Note** This is the middle expression of (103).
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Eq. (103), p.31

import Mathlib
import Definitions.Def_HeilmanMax3Cut_Bk
import Definitions.Def_HeilmanMax3Cut_nuExp
open MeasureTheory

namespace HeilmanMax3Cut

/-- **The first-mode correction multiplier `B^{(1)}(t)`.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Eq. (103), p.31:
`B^{(1)}(t) := ∫₀^∞ B(t, s) dν(s)`.

**Formalization Note.** The middle expression of (103) is the definition; its closed form is
derived in the paper via (96). -/
noncomputable def B1 (σ t : ℝ) : ℝ :=
  ∫ s, Bk σ t s ∂nuExp

end HeilmanMax3Cut


