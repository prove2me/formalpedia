-- Prove2me | Definitions.Def_DelayedGamesMAO_gammaMAO
-- name    : DelayedGamesMAO_gammaMAO
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:23:44.411499+00:00
-- url     : https://prove2.me/theorems/4fbd6a57-d5c2-4d1d-82df-550e5a813a41
-- title:
--   Optimism weight $\gamma=\max\{4L,2G/\sqrt M\}$
-- statement:
--   For constants $L,G,M>0$, the **optimism weight** of Theorem 1 is
--   $$
--   \gamma=\max\Bigl\{4L,\ \frac{2G}{\sqrt M}\Bigr\}.
--   $$
-- source:
--   Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, Optimal Learning in Games with Arbitrary Delays: Best-of-Both-Worlds for Self-Play and Adversarial Opponents, STOC 2027 submission (manuscript sha256 d17ba8b0…1247), §5.1, Theorem 1, p.12

import Mathlib

set_option autoImplicit false

namespace DelayedGamesMAO

/-- **The optimism weight of Theorem 1** `γ := max{4L, 2G/√M}`.
Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, *Optimal Learning in Games with Arbitrary Delays:
Best-of-Both-Worlds for Self-Play and Adversarial Opponents*, STOC 2027 submission manuscript
(sha256 d17ba8b0…1247), §5.1, Theorem 1, p.12. -/
noncomputable def gammaMAO (L G M : ℝ) : ℝ :=
  max (4 * L) (2 * G / Real.sqrt M)

end DelayedGamesMAO


