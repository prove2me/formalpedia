-- Prove2me | Definitions.Def_HeilmanMax3Cut_J0
-- name    : HeilmanMax3Cut_J0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:30:00.340707+00:00
-- url     : https://prove2.me/theorems/05017710-ee52-4be1-ab01-86ded2e373e7
-- title:
--   The multiplier $J_0(t)$
-- statement:
--   $$J_0(t)=\int_0^\infty R_0(t,s)\,j\bigl(a(t,s)\bigr)\,d\nu(s).$$
--
--   **Formalization Note** This is the middle expression of (101).
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Eq. (101), p.31

import Mathlib
import Definitions.Def_HeilmanMax3Cut_R0
import Definitions.Def_HeilmanMax3Cut_aR
import Definitions.Def_HeilmanMax3Cut_jA
import Definitions.Def_HeilmanMax3Cut_nuExp
open MeasureTheory

namespace HeilmanMax3Cut

/-- **The uncorrected multiplier `J₀(t)`.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Eq. (101), p.31:
`J₀(t) := ∫₀^∞ R₀(t, s) j(a) dν(s)` with `a = a(t, s)` from (96).

**Formalization Note.** A Bochner integral against `ν`; the integrand is nonnegative and at most
`R₀(t, s)/2` (`0 ≤ j ≤ 1/2`), and `∫ R₀(t, s) dν(s) = 1` (99), so it is integrable. -/
noncomputable def J0 (σ t : ℝ) : ℝ :=
  ∫ s, R0 σ t s * jA (aR σ t s) ∂nuExp

end HeilmanMax3Cut


