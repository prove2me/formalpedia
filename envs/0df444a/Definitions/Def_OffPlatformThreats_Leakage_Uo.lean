-- Prove2me | Definitions.Def_OffPlatformThreats_Leakage_Uo
-- name    : OffPlatformThreats_Leakage_Uo
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:33:46.881115+00:00
-- url     : https://prove2.me/theorems/0183583b-6492-4fdc-a9e5-d00417a2e1d7
-- title:
--   Off-platform utility rate $U_o$
-- statement:
--   A provider off the platform sets his fee to solve
--
--   $$\max_{q \ge 0} \{ q\,\lambda_o(q) - K \} \qquad (6)$$
--
--   and, at an optimal fee $Q_o$, receives the utility rate $U_o = Q_o\,\lambda_o(Q_o) - K$ (7). Here $U_o$ is the optimal value of (6), $\sup_{q \ge 0} (q\,\lambda_o(q) - K)$, which coincides with (7) whenever (6) has a maximizer (Lemma 2).
--
--   **Formalization Note** The supremum is taken in $\mathbb{R}$.
-- source:
--   He, Savin, Goh, Teo, Off-Platform Threats in On-Demand Services, SSRN 3550646 (2021-03-25 version), (6) and (7), p. 12

import Mathlib
import Definitions.Def_OffPlatformThreats_Leakage_Market
import Definitions.Def_OffPlatformThreats_Leakage_offDemand

namespace OffPlatformThreats.Leakage

/-- **Off-platform utility rate `U^j_o`.**
He, Savin, Goh & Teo, SSRN 3550646 (2021-03-25 version), (6) and (7), p. 12: an off-platform
provider solves `max_{q ∈ ℝ₊} {q λ^j_o(q) − K^j}` (6), and with an optimal solution `Q^j_o`,
`U^j_o := Q^j_o λ^j_o(Q^j_o) − K^j` (7).

`Uo m` is the optimal value of (6): the supremum over `q ≥ 0` of `q λ_o(q) − K`.

**Formalization Note.** (7) evaluates the objective of (6) at a maximizer, so it equals this
supremum whenever (6) has one; Lemma 2 shows it does, and that
`U_o = g2(1, (v − Ro)^+) − K`. The supremum is taken in `ℝ`. -/
noncomputable def Uo (m : Market) : ℝ :=
  sSup ((fun q : ℝ => q * offDemand m q - m.K) '' Set.Ici 0)

end OffPlatformThreats.Leakage


