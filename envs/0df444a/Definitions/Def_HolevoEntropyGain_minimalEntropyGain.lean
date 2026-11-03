-- Prove2me | Definitions.Def_HolevoEntropyGain_minimalEntropyGain
-- name    : HolevoEntropyGain_minimalEntropyGain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:18:02.282636+00:00
-- url     : https://prove2.me/theorems/f9820e4a-926f-4e32-99ab-a31f258e094f
-- title:
--   Minimal entropy gain $G(\Phi)$
-- statement:
--   The **minimal entropy gain** of a channel $\Phi$ on $\ell^2(I)$ is
--
--   $$
--   G(\Phi) = \inf_{\rho:\,H(\rho)<\infty}\big(H(\Phi[\rho]) - H(\rho)\big), \tag{11}
--   $$
--
--   the infimum over all states of finite entropy, taken in $[-\infty,+\infty]$. In finite dimension $d$ one has $-\log d\le G(\Phi)\le 0$; in infinite dimensions $G(\Phi)$ can be any real number and even $+\infty$.
--
--   **Formalization Note** The infimum is in `EReal`; it is over a nonempty set as soon as $I$ is nonempty (pure states have entropy $0$).
-- source:
--   Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, §2, eq. (11), p.4

import Mathlib
import Definitions.Def_HolevoEntropyGain_entropyGain

open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel)
open QAlgorithms.Papers.Independent.Frontier18.P07 (extendedEntropyNats)

namespace HolevoEntropyGain

/-- The minimal entropy gain `G(Φ) = inf_{ρ : H(ρ) < ∞} (H(Φ[ρ]) - H(ρ))`
(Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, §2, eq. (11), p.4, PDF p.4).

**Formalization Note** (R8) The infimum is in `EReal`. It is over a nonempty set as soon as `I` is
nonempty, since pure states have entropy zero, and it may be `+∞`. -/
noncomputable def minimalEntropyGain {I : Type} (Φ : Channel I I) : EReal :=
  ⨅ ρ : {ρ : State I // extendedEntropyNats ρ.coefficients < ⊤}, entropyGain Φ ρ.val

end HolevoEntropyGain


