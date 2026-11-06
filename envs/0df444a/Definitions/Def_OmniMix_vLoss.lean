-- Prove2me | Definitions.Def_OmniMix_vLoss
-- name    : OmniMix_vLoss
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:38:59.366544+00:00
-- url     : https://prove2.me/theorems/ba987b3d-966d-4c8c-ac51-0b0a90ea636c
-- title:
--   V-shaped loss $\lambda_v$ as a loss
-- statement:
--   The V-shaped loss $\lambda_v$ of Eq. (12), $\lambda_v(q,1)=(1-v)\mathbb I\{q<v\}$ and $\lambda_v(q,0)=v\mathbb I\{q\ge v\}$, viewed as a loss with values in $\mathbb R\cup\{+\infty\}$ (all its values are real).
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, §2, p.9, Eq. (12)

import Mathlib
import Definitions.Def_OmniMix_Loss
import Definitions.Def_OmniMix_vLossR

namespace OmniMix

/-- **The V-shaped loss `λ_v` as a loss.** Liu–Luo–Ratliff, *Omniprediction for All Mixable Proper Losses and Beyond*, arXiv:2610.41023, §2, p.9, Eq. (12). `vLoss v` is
`λ_v` viewed as an `EReal`-valued loss (its values are real). -/
noncomputable def vLoss (v : ℝ) : Loss := fun q y => ((vLossR v q y : ℝ) : EReal)

end OmniMix


