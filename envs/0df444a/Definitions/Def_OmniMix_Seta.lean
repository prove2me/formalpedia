-- Prove2me | Definitions.Def_OmniMix_Seta
-- name    : OmniMix_Seta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:39:10.264299+00:00
-- url     : https://prove2.me/theorems/28e5d983-59d7-4cb7-b153-8bca931211ab
-- title:
--   $S^\eta_p(h)$
-- statement:
--   $S^\eta_p(h)=F^\eta_{p,1}(h)-F^\eta_{p,0}(h)$, the difference of the two outcome factors.
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, Lemma 3.4, §3.2, p.14

import Mathlib
import Definitions.Def_OmniMix_Feta

namespace OmniMix

/-- **`S^η_p(h) = F^η_{p,1}(h) − F^η_{p,0}(h)`.** Liu–Luo–Ratliff, *Omniprediction for All Mixable Proper Losses and Beyond*, arXiv:2610.41023, Lemma 3.4, §3.2, p.14. -/
noncomputable def Seta (η p h : ℝ) : ℝ := Feta η p 1 h - Feta η p 0 h

end OmniMix


