-- Prove2me | Definitions.Def_OmniMix_bTest
-- name    : OmniMix_bTest
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:39:44.705527+00:00
-- url     : https://prove2.me/theorems/41a51277-5c14-4542-bf07-b612df2870f9
-- title:
--   Test function $b_\ell(p,q)$
-- statement:
--   For a proper loss $\ell$, the **test function** is
--   $$
--   b_\ell(p,q)=\Delta_\ell(p)-\Delta_\ell(q),
--   $$
--   which is the paper's $\Delta_\ell(\pi_\ell(p))-\Delta_\ell(q)$ with $\pi_\ell(p)=p$.
--
--   **Formalization Note** Computed in the extended reals.
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, §2, p.9

import Mathlib
import Definitions.Def_OmniMix_Loss
import Definitions.Def_OmniMix_lossDiff

namespace OmniMix

/-- **Test function `b_ℓ(p, q)`.** Liu–Luo–Ratliff, *Omniprediction for All Mixable Proper Losses and Beyond*, arXiv:2610.41023, §2, p.9: "`b_ℓ(p, q) = Δ_ℓ(π_ℓ(p)) − Δ_ℓ(q)`".

**Formalization Note.** Stated for proper losses, where `π_ℓ(p) = p` (§2, p.8), so
`b_ℓ(p,q) = Δ_ℓ(p) − Δ_ℓ(q)`. Computed in `EReal`. -/
noncomputable def bTest (ℓ : Loss) (p q : unitInterval) : EReal := lossDiff ℓ p - lossDiff ℓ q

end OmniMix


