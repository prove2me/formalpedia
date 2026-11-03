-- Prove2me | Definitions.Def_RelaxedIndexability_passiveTime
-- name    : RelaxedIndexability_passiveTime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:20:55.549789+00:00
-- url     : https://prove2.me/theorems/cb0511d2-47b0-4a98-a5cb-6a4181f422da
-- title:
--   Passive time $\hat D_\beta(\omega_1)$ of the threshold policy (39)
-- statement:
--   With $\omega$ fixed as a point in the threshold, the **passive time** of the threshold policy $\pi_{\beta,m}$ started at belief $\omega_1$ is the expected total discounted time spent passive,
--   $$
--   \hat D_{\beta}(\omega_1) = \mathbb E_{\pi_{\beta,m}}\Big[\sum_{t=1}^{\infty} \beta^{t-1}\, \mathbb 1(u(t) = 0) \,\Big|\, \omega(1) = \omega_1\Big],
--   $$
--   that is, the value of the threshold policy when the reward is $1$ in every passive slot and $0$ in every active slot.
--
--   **Formalization Note** The threshold rule (33) compares $xB'$ with $\omega B'$ and does not involve the subsidy $m$, so the passive time is defined without an $m$ argument: the paper's $\hat D_{\beta,m}$ does not depend on $m$, and the paper writes it $\hat D_\beta$.
-- source:
--   Liu, Relaxed Indexability and Index Policy for Partially Observable Restless Bandits, arXiv:2107.11939v4, (39) and the sentence after it, Theorem 3, p.22

import Mathlib
import Definitions.Def_RelaxedIndexability_policyValue
import Definitions.Def_RelaxedIndexability_thresholdValue

namespace RelaxedIndexability

variable {K : ℕ}

/-- **The passive time `D̂_β(x)`** (Liu, arXiv:2107.11939v4, (39), p.22): the expected total
discounted passive time `𝔼_{π_{β,m}}[∑_{t=1}^{∞} β^{t−1} 𝟙(u(t) = 0) | ω(1) = x]` under the threshold
policy with threshold `ω`, i.e. the value of that policy with reward `0` when active and `1` when
passive.

**Formalization Note.** The threshold rule (33) compares `x B′` with `ω B′` and does not involve
the subsidy `m`, so the passive time carries no `m` argument: its independence of `m` holds by
construction. -/
noncomputable def passiveTime (β : ℝ) (P : Matrix (Fin K) (Fin K) ℝ) (B ω : Fin K → ℝ)
    (x : Fin K → ℝ) : ℝ :=
  policyValue β P (fun _ => 0) (fun _ => 1) (thresholdRule B ω) x

end RelaxedIndexability


