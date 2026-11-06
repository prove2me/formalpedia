-- Prove2me | Definitions.Def_DelayedGamesMAO_remainder
-- name    : DelayedGamesMAO_remainder
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:28:50.337859+00:00
-- url     : https://prove2.me/theorems/ee1354cb-1b05-4577-af77-670ecc2d6a60
-- title:
--   Remainder weight $b_t=\beta_t-\sum_{k\in A_t}r^{(t)}_k$
-- statement:
--   Given a delay sequence, $\gamma$, learning rates $\eta$ and an allocation schedule $\alpha$, the **remainder weight** at time $t$ is
--   $$
--   b_t=\beta_t-\sum_{k\in A_t}r^{(t)}_k ,
--   $$
--   the part of the flow $\beta_t$ not reserved by active anchors; MAO-OMD places it on $w_t$ when computing $w_{t+1}$.
-- source:
--   Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, Optimal Learning in Games with Arbitrary Delays: Best-of-Both-Worlds for Self-Play and Adversarial Opponents, STOC 2027 submission (manuscript sha256 d17ba8b0…1247), §5.1, p.11 (after (8))

import Mathlib
import Definitions.Def_DelayedGamesMAO_beta
import Definitions.Def_DelayedGamesMAO_remWeight

set_option autoImplicit false

namespace DelayedGamesMAO

/-- **Remainder weight** `b_t := β_t − ∑_{k ∈ A_t} r_k^{(t)}`.
Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, *Optimal Learning in Games with Arbitrary Delays:
Best-of-Both-Worlds for Self-Play and Adversarial Opponents*, STOC 2027 submission manuscript
(sha256 d17ba8b0…1247), §5.1, p.11 (after (8)). -/
noncomputable def remainder (d : ℕ → ℕ) (γ : ℝ) (η : ℕ → ℝ) (α : ℕ → ℕ → ℝ) (t : ℕ) : ℝ :=
  beta d γ η t - ∑ k ∈ active d t, remWeight d γ η α t k

end DelayedGamesMAO


