-- Prove2me | Definitions.Def_DRSub4633_bPar
-- name    : DRSub4633_bPar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:57:32.076208+00:00
-- url     : https://prove2.me/theorems/09d853f6-19de-4a50-b81f-84b77a8bd5cf
-- title:
--   The parameter $b=217763/250000$
-- statement:
--   The parameter
--   $$b=\frac{217763}{250000}.$$
--   It fixes the recovery map, the coordinate threshold $s=1-b$ and all averaging weights of the construction. It is slightly larger than $\sqrt3/2$, which is what creates the slack used in Lemma A.4.
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 4, Eq. (8), p.9

import Mathlib

namespace DRSub4633

/-- **The parameter `b = 217763/250000`.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Section 4, Eq. (8), p.9:
"`b = 217763/250000`". -/
noncomputable def bPar : ℝ := 217763 / 250000

end DRSub4633


