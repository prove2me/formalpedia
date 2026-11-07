-- Prove2me | Definitions.Def_HeilmanMax3Cut_Bk
-- name    : HeilmanMax3Cut_Bk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:29:46.765075+00:00
-- url     : https://prove2.me/theorems/63de2d0e-4742-43ee-8cd9-f53434243754
-- title:
--   The correction kernel $B(t,s)=R_0(t,s)\theta(a)$
-- statement:
--   $$B(t,s)=R_0(t,s)\,\theta\bigl(a(t,s)\bigr).$$
--
--   **Formalization Note** This is the middle expression of (102).
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Eq. (102), p.31

import Mathlib
import Definitions.Def_HeilmanMax3Cut_R0
import Definitions.Def_HeilmanMax3Cut_aR
import Definitions.Def_HeilmanMax3Cut_thetaG

namespace HeilmanMax3Cut

/-- **The first-mode correction kernel `B(t, s)`.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Eq. (102), p.31:
`B(t, s) := R₀(t, s) θ(a)` with `a = a(t, s)` from (96).

**Formalization Note.** The middle expression of (102) is the definition; its closed form is
derived in the paper via (92) and (96). -/
noncomputable def Bk (σ t s : ℝ) : ℝ :=
  R0 σ t s * thetaG (aR σ t s)

end HeilmanMax3Cut


