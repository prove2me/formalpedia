-- Prove2me | Definitions.Def_DRSub4633_Itail
-- name    : DRSub4633_Itail
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:59:45.587213+00:00
-- url     : https://prove2.me/theorems/e11de010-4a30-4578-839c-911a6286db78
-- title:
--   The tail integral $I(t)$
-- statement:
--   $$I(t)=\int_t^1[c_1w(r)-\Gamma]\,dr.$$
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Lemma A.5, Eq. (127), p.48

import Mathlib
import Definitions.Def_DRSub4633_c1
import Definitions.Def_DRSub4633_wDens
import Definitions.Def_DRSub4633_Gam

namespace DRSub4633

/-- **The tail integral `I(t) = ∫_t^1 [c₁w(r) − Γ] dr`.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Lemma A.5, Eq. (127), p.48. -/
noncomputable def Itail (t : ℝ) : ℝ := ∫ r in t..1, (c1 * wDens r - Gam)

end DRSub4633


