-- Prove2me | Definitions.Def_HolevoEntropyGain_entropyGain
-- name    : HolevoEntropyGain_entropyGain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:17:01.621634+00:00
-- url     : https://prove2.me/theorems/5f9bf865-6497-4a3e-81f7-ff5e42018c34
-- title:
--   Entropy gain $H(\Phi[\rho]) - H(\rho)$
-- statement:
--   For a channel $\Phi$ and a state $\rho$ on $\ell^2(I)$, the **entropy gain** is
--
--   $$
--   H(\Phi[\rho]) - H(\rho),
--   $$
--
--   where $H(\rho) = -\operatorname{Tr}\rho\log\rho\in[0,+\infty]$ is the von Neumann entropy (natural logarithm). When $H(\rho)<\infty$ it is a well defined element of $(-\infty,+\infty]$.
--
--   **Formalization Note** The entropies are the platform's `extendedEntropyNats` (suprema over finite coordinate compressions, equal to $\sum_k\lambda_k(-\log\lambda_k)$ by Lindblad's lemma). The difference is taken in `EReal`; it is only used at $H(\rho)<\infty$, where no $\infty-\infty$ occurs.
-- source:
--   Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, §1, p.1, and proof of Proposition 1, p.3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P07

open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel)
open QAlgorithms.Papers.Independent.Frontier18.P07 (extendedEntropyNats)

namespace HolevoEntropyGain

/-- The entropy gain `H(Φ[ρ]) - H(ρ)` (Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, §1, p.1, and proof of Proposition 1, p.3, PDF pp.1, 3).

**Formalization Note** (R3, R8) Entropies are the platform's natural-log entropies in `[0, ∞]`. The gain
is computed in `EReal` and is only used at `H(ρ) < ∞`, where it is the paper's value in `(-∞, +∞]`:
`⊤ - x = ⊤` for finite `x`, and no `⊤ - ⊤` occurs. -/
noncomputable def entropyGain {I : Type} (Φ : Channel I I) (ρ : State I) : EReal :=
  (extendedEntropyNats (Φ.val ρ.coefficients)).toEReal - (extendedEntropyNats ρ.coefficients).toEReal

end HolevoEntropyGain


