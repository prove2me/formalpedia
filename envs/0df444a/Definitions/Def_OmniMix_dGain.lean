-- Prove2me | Definitions.Def_OmniMix_dGain
-- name    : OmniMix_dGain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:39:10.527195+00:00
-- url     : https://prove2.me/theorems/45b272b1-120e-4e42-8761-3a7fe203be61
-- title:
--   Properness gain $d_\ell(p,q)$
-- statement:
--   For a proper loss $\ell$, the **properness gain** is
--   $$
--   d_\ell(p,q)=\mathbb E_{Y\sim\mathrm{Ber}(p)}[\ell(q,Y)-\ell(p,Y)],
--   $$
--   the paper's $\mathbb E_{Y\sim\mathrm{Ber}(p)}[\ell(q,Y)-\ell(\pi_\ell(p),Y)]$ with $\pi_\ell(p)=p$. It is nonnegative by properness.
--
--   **Formalization Note** Computed in the extended reals.
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, §2, p.9

import Mathlib
import Definitions.Def_OmniMix_Loss
import Definitions.Def_OmniMix_bern

namespace OmniMix

/-- **Properness gain `d_ℓ(p, q)`.** Liu–Luo–Ratliff, *Omniprediction for All Mixable Proper Losses and Beyond*, arXiv:2610.41023, §2, p.9:
"`d_ℓ(p, q) = E_{Y∼Ber(p)}[ℓ(q, Y) − ℓ(π_ℓ(p), Y)]`".

**Formalization Note.** Stated for proper losses, where `π_ℓ(p) = p` (§2, p.8). Computed in `EReal`
with the Bernoulli expectation `bern`. -/
noncomputable def dGain (ℓ : Loss) (p q : unitInterval) : EReal :=
  bern p (fun y => ℓ q y - ℓ p y)

end OmniMix


