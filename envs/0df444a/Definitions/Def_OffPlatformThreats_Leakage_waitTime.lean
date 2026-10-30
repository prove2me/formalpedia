-- Prove2me | Definitions.Def_OffPlatformThreats_Leakage_waitTime
-- name    : OffPlatformThreats_Leakage_waitTime
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:29:14.065907+00:00
-- url     : https://prove2.me/theorems/13cd56f7-2444-4749-a5f4-0e3098b109a1
-- title:
--   Heavy-traffic expected waiting time $W(n, \lambda)$
-- statement:
--   For a queue served by $n$ providers of service rate $\mu$ that receives demand at rate $\lambda$, the expected waiting time in the heavy-traffic approximation is
--
--   $$W(n, \lambda) = \frac{\lambda}{n(\mu - \lambda)}\,\phi .$$
--
--   With $n = C$ it is the on-platform waiting time $W_p(C, \lambda)$ of (2), and with $n = 1$ the off-platform waiting time $W_o(1, \lambda)$ of (3). The paper uses these formulas only for a stable system, $\lambda/\mu < 1$.
--
--   **Formalization Note** The stability proviso is not part of this function; it is a clause of the demand equilibrium conditions.
-- source:
--   He, Savin, Goh, Teo, Off-Platform Threats in On-Demand Services, SSRN 3550646 (2021-03-25 version), (2) and (3), p. 11

import Mathlib
import Definitions.Def_OffPlatformThreats_Leakage_Market

namespace OffPlatformThreats.Leakage

/-- **Expected waiting time in the heavy-traffic approximation.**
He, Savin, Goh & Teo, SSRN 3550646 (2021-03-25 version), (2) and (3), p. 11:
`W_p(C, λ) := λ / (C (µ − λ)) · φ` for a common queue of `C` providers, and
`W_o(1, λ) := λ / (µ − λ) · φ` for a single off-platform provider, "provided that the system is
stable, i.e., that λ/µ < 1".

`waitTime m n lam` is `W_p(n, λ)`; with `n = 1` it is `W_o(1, λ)`.

**Formalization Note.** The stability proviso `λ < µ` is not part of this function; it is a
clause of the demand equilibrium conditions `OnDemandEq` and `OffDemandEq`, which use it. -/
noncomputable def waitTime (m : Market) (n : ℕ) (lam : ℝ) : ℝ :=
  lam / ((n : ℝ) * (m.mu - lam)) * m.phi

end OffPlatformThreats.Leakage


