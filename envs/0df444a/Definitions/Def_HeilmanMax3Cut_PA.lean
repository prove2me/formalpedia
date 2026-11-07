-- Prove2me | Definitions.Def_HeilmanMax3Cut_PA
-- name    : HeilmanMax3Cut_PA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:27:59.916408+00:00
-- url     : https://prove2.me/theorems/733de4e7-9f2e-4837-8d64-fbc574e0ff65
-- title:
--   $P(a)=\partial_1K_a(b,b)$
-- statement:
--   With $b=1/3$,
--
--   $$P(a)=\frac{\partial}{\partial p}K_a(p,b)\Big|_{p=b},$$
--
--   the derivative of the opposing-arc overlap in its first argument at the centre of the simplex.
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Eq. (65), p.23; b = 1/3 by (57), p.22

import Mathlib
import Definitions.Def_HeilmanMax3Cut_Karc

namespace HeilmanMax3Cut

/-- **`P(a) = ∂₁K_a(b, b)`.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Eq. (65), p.23, with `b = 1/3` (57): "`P(a) := ∂₁K_a(b, b)` …
Here `∂₁` denotes differentiation in the first scalar argument."

**Formalization Note.** `deriv` of `p ↦ K_a(p, 1/3)` at the interior point `p = 1/3`; the map is
differentiable there (the paper's (76)). -/
noncomputable def PA (a : ℝ) : ℝ :=
  deriv (fun p => Karc a p (1 / 3)) (1 / 3)

end HeilmanMax3Cut


