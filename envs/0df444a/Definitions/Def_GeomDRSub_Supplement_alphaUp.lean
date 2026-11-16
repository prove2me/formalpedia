-- Prove2me | Definitions.Def_GeomDRSub_Supplement_alphaUp
-- name    : GeomDRSub_Supplement_alphaUp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:51:45.863358+00:00
-- url     : https://prove2.me/theorems/402c19a6-246f-400f-94db-548551a4f9a0
-- title:
--   The upper profile $\bar\alpha(\zeta)=\min\{U(\zeta),C(\zeta)\}$
-- statement:
--   $$\bar\alpha(\zeta)=\min\{U(\zeta),C(\zeta)\}\qquad(\zeta\in[0,1])$$
--   (Eq. (186)). It is the combined offline upper bound. The paper prints it with an overline, to distinguish it from the lower profile $\underline\alpha(\zeta)=4c_\zeta/(2c_\zeta+1)^2$ of (11).
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Section 6.5, p.46, Eq. (186)

import Mathlib
import Definitions.Def_GeomDRSub_Supplement_U
import Definitions.Def_GeomDRSub_Supplement_C

namespace GeomDRSub.Supplement

/-- **The upper profile `ᾱ(ζ) = min{U(ζ), C(ζ)}`**, Eq. (186). Aggarwal–Lu, *Geometry-Dependent Online and Offline Approximation for Non-Monotone
DR-Submodular Maximization*, arXiv:2610.00545, Section 6.5, p.46.
The paper prints it with an overline (`ᾱ`), distinct from the underlined lower profile
`α̲(ζ) = 4c_ζ/(2c_ζ + 1)²` of (11) (`GeomDRSub.alphaLow`); the text layer flattens both to `α(ζ)`. -/
noncomputable def alphaUp (ζ : ℝ) : ℝ :=
  min (U ζ) (C ζ)

end GeomDRSub.Supplement


