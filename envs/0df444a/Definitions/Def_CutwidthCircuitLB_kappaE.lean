-- Prove2me | Definitions.Def_CutwidthCircuitLB_kappaE
-- name    : CutwidthCircuitLB_kappaE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:24:30.287436+00:00
-- url     : https://prove2.me/theorems/91bb173f-468b-4581-bc02-7f3eb5f84b22
-- title:
--   The constant $\kappa_E = \frac{3}{2\pi}\arccos\frac{1+2\sqrt2}{4}$
-- statement:
--   The constant
--   $$
--   \kappa_E = \frac{3}{2\pi} \arccos \frac{1 + 2\sqrt 2}{4} = 0.1403509\ldots
--   $$
--   It is the probability bound for a vertex of the infinite 3-regular tree to be open at a threshold in the Gaussian edge-score ordering of Appendix A. Theorem 4.6 bounds the cubic cutwidth constant by $2\kappa_E$.
-- source:
--   McGuire–Schlesinger–Williams, Explicit functions requiring larger than 4.5n size circuits, STOC 2027 submission (manuscript sha256 ed87148f…cfa3), Section 1.1, p.3; Theorem 4.6, p.14; Appendix A, p.21

import Mathlib

namespace CutwidthCircuitLB

/-- The constant `κ_E = (3/(2π)) · arccos((1 + 2√2)/4) = 0.1403509…` (McGuire–Schlesinger–Williams, *Explicit functions requiring larger than 4.5n size circuits*, STOC 2027 submission manuscript (sha256 ed87148f…cfa3), §1.1, p.3, Theorem 4.6,
p.14, and Appendix A, p.21). -/
noncomputable def kappaE : ℝ :=
  3 / (2 * Real.pi) * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)

end CutwidthCircuitLB


