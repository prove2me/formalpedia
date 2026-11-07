-- Prove2me | Definitions.Def_HeilmanMax3Cut_Fv
-- name    : HeilmanMax3Cut_Fv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:28:12.065131+00:00
-- url     : https://prove2.me/theorems/d205348d-6cca-4c16-862e-9616567002e6
-- title:
--   $F_v(t)$
-- statement:
--   With $d=1-\sigma^2$, $\kappa=\sigma^2/d$ and $b_v(t)$ as in (116),
--
--   $$F_v(t)=e^{-\kappa t}\Bigl[1-\sqrt\pi\,b_v(t)\,e^{b_v(t)^2}\,\mathrm{erfc}\bigl(b_v(t)\bigr)\Bigr],\qquad t\ge0,$$
--
--   where $\mathrm{erfc}(z)=\frac{2}{\sqrt\pi}\int_z^\infty e^{-u^2}\,du$.
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Eqs. (115)–(117), p.32

import Mathlib
import Definitions.Def_FickDiffusion_defs
import Definitions.Def_HeilmanMax3Cut_bv
open Real FickDiffusion

namespace HeilmanMax3Cut

/-- **`F_v(t)`.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Eqs. (115), (117), p.32: with `κ = σ²/d`, `d = 1 − σ²`,
`F_v(t) := e^{−κt} [1 − √π b_v(t) e^{b_v(t)²} erfc(b_v(t))]`, `t ≥ 0`,
where `erfc(z) := (2/√π) ∫_z^∞ e^{−u²} du`.

**Formalization Note.** `erfc` is the published `FickDiffusion.erfc`, the same formula. -/
noncomputable def Fv (σ v t : ℝ) : ℝ :=
  Real.exp (-(σ ^ 2 / (1 - σ ^ 2)) * t) *
    (1 - Real.sqrt π * bv σ v t * Real.exp (bv σ v t ^ 2) * erfc (bv σ v t))

end HeilmanMax3Cut


