-- Prove2me | Definitions.Def_DRSub4633_WTail
-- name    : DRSub4633_WTail
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:59:43.052363+00:00
-- url     : https://prove2.me/theorems/24179d37-9742-4cab-b313-e54d09956795
-- title:
--   The tail $W(t)=\int_t^1[w+\varpi]$
-- statement:
--   For a time $t$,
--   $$W(t)=\int_t^1 [w(r)+\varpi(r)]\,dr .$$
--   It is the tail of the averaging measure $\mu(dt)=[w(t)+\varpi(t)]\,dt$.
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 4.1, Eq. (18), p.11

import Mathlib
import Definitions.Def_DRSub4633_wDens
import Definitions.Def_DRSub4633_varpiDens

namespace DRSub4633

/-- **The tail `W(t) = ∫_t^1 [w(r) + ϖ(r)] dr`.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Section 4.1, Eq. (18), p.11. -/
noncomputable def WTail (t : ℝ) : ℝ := ∫ r in t..1, (wDens r + varpiDens r)

end DRSub4633


