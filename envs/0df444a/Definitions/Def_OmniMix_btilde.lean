-- Prove2me | Definitions.Def_OmniMix_btilde
-- name    : OmniMix_btilde
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:40:06.184349+00:00
-- url     : https://prove2.me/theorems/e5ee0c7e-f0fb-45b1-b6e2-acc3c037edb8
-- title:
--   Corrected threshold test $\tilde b^\eta_v(p,q)$
-- statement:
--   $$
--   \tilde b^\eta_v(p,q)=S^\eta_p\big(b_v(p,q)\big)=F^\eta_{p,1}(b_v(p,q))-F^\eta_{p,0}(b_v(p,q)).
--   $$
--   It replaces $\eta\,b_v$ in the test function of Algorithm 2.
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, §3.2, p.14, Eq. (24)

import Mathlib
import Definitions.Def_OmniMix_Seta
import Definitions.Def_OmniMix_bV

namespace OmniMix

/-- **Corrected threshold test `b̃^η_v(p, q) = S^η_p(b_v(p, q))`.** Liu–Luo–Ratliff, *Omniprediction for All Mixable Proper Losses and Beyond*, arXiv:2610.41023, §3.2, p.14, Eq. (24). -/
noncomputable def btilde (η v p q : ℝ) : ℝ := Seta η p (bV v p q)

end OmniMix


