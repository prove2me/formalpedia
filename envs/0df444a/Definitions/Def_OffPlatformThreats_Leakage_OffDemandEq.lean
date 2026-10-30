-- Prove2me | Definitions.Def_OffPlatformThreats_Leakage_OffDemandEq
-- name    : OffPlatformThreats_Leakage_OffDemandEq
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:30:40.07581+00:00
-- url     : https://prove2.me/theorems/194c8f63-348d-4176-ab0f-ea0ae59c69fa
-- title:
--   Equilibrium condition (5) for off-platform demand
-- statement:
--   Consider a provider off the platform who charges the fee $q$. A demand rate $\lambda$ is an equilibrium demand rate for him if
--
--   1. when $v > q + R_o$: $0 \le \lambda < \mu$ and $v - q - c\,W_o(1, \lambda) - R_o = 0$;
--   2. otherwise: $\lambda = 0$.
--
--   This is the second half of (5).
--
--   **Formalization Note** The paper's case condition also contains $n_o \ge 1$; the rate is evaluated for a provider who is off the platform, so that condition holds and is omitted. As on the platform, $0 \le \lambda < \mu$ is part of the first case.
-- source:
--   He, Savin, Goh, Teo, Off-Platform Threats in On-Demand Services, SSRN 3550646 (2021-03-25 version), (5), last two lines, p. 11

import Mathlib
import Definitions.Def_OffPlatformThreats_Leakage_Market
import Definitions.Def_OffPlatformThreats_Leakage_waitTime

namespace OffPlatformThreats.Leakage

/-- **Equilibrium condition (5) for off-platform demand.**
He, Savin, Goh & Teo, SSRN 3550646 (2021-03-25 version), (5), last two lines, p. 11:
"`v^j − q^j_{o,i} − c W_o(1, λ^j_{o,i}) − Ro = 0`, if `n^j_o ≥ 1` and `v^j > q^j_{o,i} + Ro`;
`λ^j_{o,i} = 0`, if `n^j_o = 0` or `v^j ≤ q^j_{o,i} + Ro`."

`OffDemandEq m q lam` says that `lam` is the equilibrium demand rate of an off-platform provider
who charges the fee `q`.

**Formalization Note.** The rate is evaluated for a provider who is off the platform, so the
printed condition `n^j_o ≥ 1` always holds and is omitted. As in `OnDemandEq`, the stability
proviso `λ < µ` of (3) and `0 ≤ λ` are part of the first case. -/
def OffDemandEq (m : Market) (q lam : ℝ) : Prop :=
  if q + m.Ro < m.v then
    0 ≤ lam ∧ lam < m.mu ∧ m.v - q - m.c * waitTime m 1 lam - m.Ro = 0
  else
    lam = 0

end OffPlatformThreats.Leakage


