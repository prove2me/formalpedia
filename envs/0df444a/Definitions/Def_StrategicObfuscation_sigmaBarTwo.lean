-- Prove2me | Definitions.Def_StrategicObfuscation_sigmaBarTwo
-- name    : StrategicObfuscation_sigmaBarTwo
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:51:03.362185+00:00
-- url     : https://prove2.me/theorems/95ef6010-7c63-4719-864d-5d6154c442da
-- title:
--   The threshold $\bar\sigma_2(p)$
-- statement:
--   The threshold $\bar\sigma_2$ is the largest resource level at which, under maximal obfuscation, the benefit of approving an uncertified proposal outweighs the cost:
--
--   $$\bar\sigma_2=\sup\{\sigma\in[0,1] : f(\sigma)>0\}.$$
--
--   **Formalization Note** The paper defines $\bar\sigma_2$ as the root of $f$. For continuous $f$ the two agree, and the supremum needs no continuity. If $f\le 0$ on all of $[0,1]$ the set is empty and Lean's `sSup` returns $0$, so that no $\sigma$ lies below the threshold, which is the intended meaning.
-- source:
--   Figueroa & Lemus, The Benefit of the Doubt: Decision Making under Strategic Obfuscation, SSRN 3840423 (version of April 4, 2022), §3, p.12, and proof of Proposition 1, Claim, p.27

import Mathlib
import Definitions.Def_StrategicObfuscation_gap

open Set

namespace StrategicObfuscation

/-- **The threshold `σ̄2(p)`.**
Figueroa & Lemus, *The Benefit of the Doubt: Decision Making under Strategic Obfuscation*,
SSRN 3840423 (version of April 4, 2022), §3, p.12 (PDF p.12), and proof of Proposition 1, Claim,
p.27 (PDF p.27): "The threshold σ̄2 is the reviewer's maximum level of resources such that at the
maximum obfuscation level, e∗ = e(1, σ), the benefit of approving an uncertified proposal outweighs
the cost."

**Formalization Note** `σ̄2` is the supremum over `σ ∈ [0, 1]` of those with `0 < f(σ)`. The paper
defines it as the root of `f`. For continuous `f` the two agree (milestone M5), and the supremum
needs no continuity. On an empty set `sSup` returns `0`: this happens when `f(σ) ≤ 0` on all of
`[0, 1]`, in which case no resource level has `f(σ) > 0` and every interval of the form `(σ̄1, σ̄2)` is
empty. The set is bounded by `1`. -/
noncomputable def sigmaBarTwo (π : ℝ → ℝ → ℝ) (V c p : ℝ) (E : ℝ → ℝ → ℝ) : ℝ :=
  sSup {σ ∈ Icc (0 : ℝ) 1 | 0 < gap π V c p E σ}

end StrategicObfuscation


