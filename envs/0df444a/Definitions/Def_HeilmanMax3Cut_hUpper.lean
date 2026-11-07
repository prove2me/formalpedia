-- Prove2me | Definitions.Def_HeilmanMax3Cut_hUpper
-- name    : HeilmanMax3Cut_hUpper
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:36:56.428346+00:00
-- url     : https://prove2.me/theorems/9011c9ac-25e1-4b0e-bb5c-e95a68b2fbc4
-- title:
--   $h_{\mathrm{upper}}(\sigma)$
-- statement:
--   $$h_{\mathrm{upper}}(\sigma)=\Bigl(\int_0^\infty\!\!\int_0^\infty\frac{E_*(t,s)^2}{J_*(t)J_*(s)}\,d\nu(t)\,d\nu(s)\Bigr)^{1/2}\in[0,\infty].$$
--
--   **Formalization Note** As for $h_{\mathrm{lower}}$: a Lebesgue integral with values in $[0,\infty]$.
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Eq. (112), p.32

import Mathlib
import Definitions.Def_HeilmanMax3Cut_Est
import Definitions.Def_HeilmanMax3Cut_Jst
import Definitions.Def_HeilmanMax3Cut_nuExp
open MeasureTheory

namespace HeilmanMax3Cut

/-- **`h_upper(σ)`.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Eq. (112), p.32:
`h_upper(σ) := (∫₀^∞ ∫₀^∞ E_*(t, s)² / (J_*(t) J_*(s)) dν(t) dν(s))^{1/2}`.

**Formalization Note.** As for `hLower`: a lower Lebesgue integral in `[0, ∞]`, so the value may be
`+∞` and is never a junk `0`. -/
noncomputable def hUpper (σ : ℝ) : ENNReal :=
  (∫⁻ t, ∫⁻ s, ENNReal.ofReal (Est σ t s ^ 2 / (Jst σ t * Jst σ s)) ∂nuExp ∂nuExp) ^ (1 / 2 : ℝ)

end HeilmanMax3Cut


