-- Prove2me | Definitions.Def_OmniMix_lossDiff
-- name    : OmniMix_lossDiff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:38:54.944409+00:00
-- url     : https://prove2.me/theorems/16813e80-d6f5-4bd4-8d5e-ac1a9c02bad8
-- title:
--   Loss difference $\Delta_\ell(q)=\ell(q,1)-\ell(q,0)$
-- statement:
--   For a loss $\ell$ and a prediction $q$, the **loss difference** between the two outcomes is $\Delta_\ell(q)=\ell(q,1)-\ell(q,0)$.
--
--   **Formalization Note** Computed in the extended reals.
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, §2, p.9

import Mathlib
import Definitions.Def_OmniMix_Loss

namespace OmniMix

/-- **Loss difference `Δ_ℓ(q)`.** Liu–Luo–Ratliff, *Omniprediction for All Mixable Proper Losses and Beyond*, arXiv:2610.41023, §2, p.9: "write the loss difference between two
outcomes at the same prediction `q` as `Δ_ℓ(q) = ℓ(q, 1) − ℓ(q, 0)`".

**Formalization Note.** Computed in `EReal`. -/
noncomputable def lossDiff (ℓ : Loss) (q : unitInterval) : EReal := ℓ q true - ℓ q false

end OmniMix


