-- Prove2me | Definitions.Def_OffPlatformThreats_Leakage_OnDemandEq
-- name    : OffPlatformThreats_Leakage_OnDemandEq
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:29:57.428604+00:00
-- url     : https://prove2.me/theorems/d39e7d28-6381-4b73-bb8b-713af389b9a0
-- title:
--   Equilibrium condition (5) for on-platform demand
-- statement:
--   Consider a provider on the platform who charges the fee $q$ and shares a common queue with the $C$ providers (himself included) who charge the same fee. A demand rate $\lambda$ is an equilibrium demand rate for him if
--
--   1. when $C \ge 1$ and $v > q$: $0 \le \lambda < \mu$ and $v - q - c\,W_p(C, \lambda) = 0$, i.e. customers are indifferent between this service and their outside option;
--   2. otherwise ($C = 0$ or $v \le q$): $\lambda = 0$.
--
--   This is the first half of (5).
--
--   **Formalization Note** The waiting time (2) is defined only for a stable queue, so $\lambda < \mu$ is part of the first case, together with $\lambda \ge 0$; without it the equation has a second, spurious root.
-- source:
--   He, Savin, Goh, Teo, Off-Platform Threats in On-Demand Services, SSRN 3550646 (2021-03-25 version), (5), first two lines, p. 11

import Mathlib
import Definitions.Def_OffPlatformThreats_Leakage_Market
import Definitions.Def_OffPlatformThreats_Leakage_waitTime

namespace OffPlatformThreats.Leakage

/-- **Equilibrium condition (5) for on-platform demand.**
He, Savin, Goh & Teo, SSRN 3550646 (2021-03-25 version), (5), first two lines, p. 11:
"`v^j − q^j_{p,ℓ} − c W_p(C^j_{p,ℓ}, λ^j_{p,ℓ}) = 0`, if `C^j_{p,ℓ} ≥ 1` and `v^j > q^j_{p,ℓ}`;
`λ^j_{p,ℓ} = 0`, if `C^j_{p,ℓ} = 0` or `v^j ≤ q^j_{p,ℓ}`."

`OnDemandEq m C q lam` says that `lam` is an equilibrium demand rate of a provider who charges
the fee `q` and shares a queue with `C` providers charging the same fee (`C` counts himself).

**Formalization Note.** The waiting time (2) is defined only for a stable system, `λ/µ < 1`
(p. 11), and a demand rate is nonnegative; both are part of the first case here
(`0 ≤ lam ∧ lam < µ`). Without `lam < µ` the equation has a second, spurious root. -/
def OnDemandEq (m : Market) (C : ℕ) (q lam : ℝ) : Prop :=
  if 1 ≤ C ∧ q < m.v then
    0 ≤ lam ∧ lam < m.mu ∧ m.v - q - m.c * waitTime m C lam = 0
  else
    lam = 0

end OffPlatformThreats.Leakage


