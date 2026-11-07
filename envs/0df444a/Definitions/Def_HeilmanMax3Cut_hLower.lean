-- Prove2me | Definitions.Def_HeilmanMax3Cut_hLower
-- name    : HeilmanMax3Cut_hLower
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:36:36.167307+00:00
-- url     : https://prove2.me/theorems/c4a2d0f3-3496-4ed3-b315-2db3674a9d42
-- title:
--   $h_{\mathrm{lower}}(\sigma)$
-- statement:
--   $$h_{\mathrm{lower}}(\sigma)=\Bigl(\int_0^\infty\!\!\int_0^\infty\frac{R_*(t,s)^2}{J_*(t)J_*(s)}\,d\nu(t)\,d\nu(s)\Bigr)^{1/2}\in[0,\infty].$$
--
--   **Formalization Note** The integral is a Lebesgue integral of a nonnegative function with values in $[0,\infty]$, so $h_{\mathrm{lower}}$ may be $+\infty$ and is never a default value of a non-integrable function.
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Eq. (111), p.32

import Mathlib
import Definitions.Def_HeilmanMax3Cut_Rst
import Definitions.Def_HeilmanMax3Cut_Jst
import Definitions.Def_HeilmanMax3Cut_nuExp
open MeasureTheory

namespace HeilmanMax3Cut

/-- **`h_lower(σ)`.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Eq. (111), p.32:
`h_lower(σ) := (∫₀^∞ ∫₀^∞ R_*(t, s)² / (J_*(t) J_*(s)) dν(t) dν(s))^{1/2}`.

**Formalization Note.** The integral is a lower Lebesgue integral in `[0, ∞]` of the nonnegative
integrand (`J_* ≥ 0`), so `h_lower` may be `+∞` and is never a junk `0` from a non-integrable
square. `J_*` vanishes only at `t = 0` (the paper's (128)), a `ν`-null point. -/
noncomputable def hLower (σ : ℝ) : ENNReal :=
  (∫⁻ t, ∫⁻ s, ENNReal.ofReal (Rst σ t s ^ 2 / (Jst σ t * Jst σ s)) ∂nuExp ∂nuExp) ^ (1 / 2 : ℝ)

end HeilmanMax3Cut


