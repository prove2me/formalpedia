-- Prove2me | Definitions.Def_ErlangA_Abandonment_Supplement_psi
-- name    : ErlangA_Abandonment_Supplement_psi
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T09:51:51.838275+00:00
-- url     : https://prove2.me/theorems/eb9f7164-b484-4640-9bc3-36d69b35a887
-- title:
--   The normal-tail ratio $\Psi(x,y)$
-- statement:
--   Write $\phi$ for the standard normal density and $\Phi$ for its cumulative distribution function. For finite real $x,y$, define
--
--   $$\Psi(x,y)=\frac{\phi(x)}{1-\Phi(x+y)}.$$
--
--   The denominator is strictly positive for every finite $x+y$. This is the function used in Theorem 3's positive stationary tail. The standard normal density, distribution and hazard rate, and the function $w$, are imported from the existing published definitions.
-- source:
--   Garnett, Mandelbaum & Reiman, Designing a Call Center with Impatient Customers, M&SOM 4(3), 2002, p. 217, Theorem 3, definitions of w and Ψ

import Mathlib
import Definitions.Def_DimCallCenters_Rationalized_delayFn

namespace ErlangA.Abandonment.Supplement

/-- The function Ψ(x,y)=φ(x)/(1−Φ(x+y)), Theorem 3, p.217. Its arguments in the theorem
are finite reals. The normal survival denominator is strictly positive there. -/
noncomputable def psi (x y : ℝ) : ℝ :=
  DimCallCenters.Rationalized.stdPdf x / (1 - DimCallCenters.Rationalized.stdCdf (x + y))

end ErlangA.Abandonment.Supplement


