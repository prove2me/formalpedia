-- Prove2me | Definitions.Def_DRSub4633_kappa
-- name    : DRSub4633_kappa
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:01:08.225645+00:00
-- url     : https://prove2.me/theorems/55f5a378-cf9c-4fa0-93c5-f4b456b88e48
-- title:
--   The weight $\kappa=bW$
-- statement:
--   The small-coordinate weight
--   $$\kappa(t)=b\,W(t).$$
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 4.1, Eq. (19), p.11

import Mathlib
import Definitions.Def_DRSub4633_bPar
import Definitions.Def_DRSub4633_WTail

namespace DRSub4633

/-- **The small-coordinate weight `κ(t) = bW(t)`.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Section 4.1, Eq. (19), p.11. -/
noncomputable def kappa (t : ℝ) : ℝ := bPar * WTail t

end DRSub4633


