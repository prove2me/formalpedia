-- Prove2me | Definitions.Def_OmniMix_IsProper
-- name    : OmniMix_IsProper
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:38:59.548285+00:00
-- url     : https://prove2.me/theorems/52f82cae-9c0e-48ea-99e5-eac4bce8b81d
-- title:
--   Proper loss
-- statement:
--   A loss $\ell$ is **proper** if
--   $$
--   \mathbb E_{Y\sim\mathrm{Ber}(p)}[\ell(p,Y)]\le\mathbb E_{Y\sim\mathrm{Ber}(p)}[\ell(q,Y)]\qquad\text{for all }p,q\in[0,1],
--   $$
--   that is, predicting $p$ is optimal when the outcome is drawn from $\mathrm{Ber}(p)$. For a proper loss the post-processing map $\pi_\ell$ is the identity, $\pi_\ell(p)=p$.
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, §1, p.1 and §2, p.8

import Mathlib
import Definitions.Def_OmniMix_Loss
import Definitions.Def_OmniMix_bern

namespace OmniMix

/-- **Proper loss.** Liu–Luo–Ratliff, *Omniprediction for All Mixable Proper Losses and Beyond*, arXiv:2610.41023, §1, p.1 and §2, p.8: "A loss `ℓ` is proper if
`E_{Y∼Ber(p)}[ℓ(p, Y)] ≤ E_{Y∼Ber(p)}[ℓ(q, Y)], ∀p, q ∈ [0, 1]`".

**Formalization Note.** The Bernoulli expectation is `bern`, computed in `EReal` (`0 · ⊤ = 0`). -/
def IsProper (ℓ : Loss) : Prop :=
  ∀ p q : unitInterval, bern p (ℓ p) ≤ bern p (ℓ q)

end OmniMix


