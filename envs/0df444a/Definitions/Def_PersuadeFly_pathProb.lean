-- Prove2me | Definitions.Def_PersuadeFly_pathProb
-- name    : PersuadeFly_pathProb
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:29:13.592505+00:00
-- url     : https://prove2.me/theorems/2b27ac80-e5e3-4d15-84b5-09691237cc95
-- title:
--   The law of a path $(\omega_t,a_t)_{t\in[T]}$
-- statement:
--   When the states $\omega_t$ are drawn independently from $\mu^*$ and, given $(h_t,\omega_t)$, the recommendation $a_t$ is drawn from $\sigma[h_t](\omega_t,\cdot)$, the probability of the path $(\omega_t,a_t)_{t\in[T]}$ is
--   $$
--   \prod_{t\in[T]}\mu^*(\omega_t)\,\sigma[h_t](\omega_t,a_t).
--   $$
--
--   **Formalization Note** Additional randomization of the algorithm (a random tie-break) is covered by conditioning on its seed: each seed gives one deterministic selection rule.
-- source:
--   Zu, Iyer, Xu, Learning to Persuade on the Fly: Robustness Against Ignorance, arXiv:2102.10156v2, §2, pp.11–13

import Mathlib
import Definitions.Def_PersuadeFly_historyAt

namespace PersuadeFly

/-- **The law of a path under `μ*` and a signaling algorithm.** Zu, Iyer, Xu, *Learning to Persuade on the Fly: Robustness Against Ignorance*, arXiv:2102.10156v2, §2, pp.11–13: the states `ω_t`
are drawn iid from `μ*`, and given `(h_t, ω_t)` the recommendation `a_t` is drawn from
`σ(h_t, ω_t, ·)`. The probability of the path `(ω_t, a_t)_{t ∈ [T]}` is
`∏_{t ∈ [T]} μ*(ω_t) σ(h_t, ω_t, a_t)`.

**Formalization Note** An explicit finite product on `Fin T → Ω × A`. Any further randomization of the
algorithm (a random tie-break) is covered by conditioning on its seed: each seed gives one `alg`. -/
def pathProb {Ω A : Type} (μ : Ω → ℝ) (alg : (t : ℕ) → (Fin t → Ω × A) → Ω → A → ℝ) (T : ℕ)
    (path : Fin T → Ω × A) : ℝ :=
  ∏ t : Fin T, μ (path t).1 * alg t (historyAt path t) (path t).1 (path t).2

end PersuadeFly


