-- Prove2me | Definitions.Def_HeilmanMax3Cut_K0
-- name    : HeilmanMax3Cut_K0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:30:22.427202+00:00
-- url     : https://prove2.me/theorems/697c48ee-a7e8-4e01-b472-d8960fd60d60
-- title:
--   The radial kernel $K_0(t,s)=R_0(t,s)\tau(a)$
-- statement:
--   $$K_0(t,s)=R_0(t,s)\,\tau\bigl(a(t,s)\bigr).$$
--
--   **Formalization Note** This is the middle expression of (100); the paper's closed form on its right is derived via (72).
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Eq. (100), p.31

import Mathlib
import Definitions.Def_HeilmanMax3Cut_R0
import Definitions.Def_HeilmanMax3Cut_aR
import Definitions.Def_HeilmanMax3Cut_tauA

namespace HeilmanMax3Cut

/-- **The uncorrected radial kernel `K₀(t, s)`.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Eq. (100), p.31: `K₀(t, s) := R₀(t, s) τ(a)`
with `a = a(t, s)` from (96).

**Formalization Note.** The middle expression of (100) is the definition; its right-hand closed
form is derived in the paper via (72). -/
noncomputable def K0 (σ t s : ℝ) : ℝ :=
  R0 σ t s * tauA (aR σ t s)

end HeilmanMax3Cut


