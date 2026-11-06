-- Prove2me | Definitions.Def_OmniMix_IsLipschitzLoss
-- name    : OmniMix_IsLipschitzLoss
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:38:53.893447+00:00
-- url     : https://prove2.me/theorems/a4b90414-0fa5-4ddc-8d02-d61f6f1efc62
-- title:
--   $L$-Lipschitz loss
-- statement:
--   A loss $\ell$ is **$L$-Lipschitz** if both partial losses $\ell(\cdot,0)$ and $\ell(\cdot,1)$ are real-valued and
--   $$
--   |\ell(p,y)-\ell(q,y)|\le L\,|p-q|\qquad\text{for all }p,q\in[0,1],\ y\in\{0,1\}.
--   $$
--
--   **Formalization Note** The difference $|\ell(p,y)-\ell(q,y)|$ presupposes finite values, so real-valuedness is part of the definition.
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, §2, p.9

import Mathlib
import Definitions.Def_OmniMix_Loss

namespace OmniMix

/-- **L-Lipschitz loss.** Liu–Luo–Ratliff, *Omniprediction for All Mixable Proper Losses and Beyond*, arXiv:2610.41023, §2, p.9: "a loss `ℓ` is L-Lipschitz if its partial loss
function `ℓ(·, y)` is L-Lipschitz for each `y ∈ {0, 1}`, that is `|ℓ(p, y) − ℓ(q, y)| ≤ L|p − q|` for
all `p, q ∈ [0, 1]`".

**Formalization Note.** The difference `|ℓ(p,y) − ℓ(q,y)|` presupposes finite values, so the
definition requires both partial losses to be real-valued (`≠ ⊤`, `≠ ⊥`) and states the bound for
their real values. -/
def IsLipschitzLoss (L : ℝ) (ℓ : Loss) : Prop :=
  (∀ p y, ℓ p y ≠ ⊤ ∧ ℓ p y ≠ ⊥) ∧
    ∀ (p q : unitInterval) (y : Bool), |(ℓ p y).toReal - (ℓ q y).toReal| ≤ L * |(p : ℝ) - q|

end OmniMix


