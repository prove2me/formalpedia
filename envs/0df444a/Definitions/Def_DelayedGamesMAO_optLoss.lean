-- Prove2me | Definitions.Def_DelayedGamesMAO_optLoss
-- name    : DelayedGamesMAO_optLoss
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:24:38.975195+00:00
-- url     : https://prove2.me/theorems/aa4fb316-d2fc-4527-bd06-4fc0774163a4
-- title:
--   Optimistic loss vector $\ell_t=h_{t+1}+\sum_{s\in N_t}(g_s-h_s)$
-- statement:
--   Given a delay sequence, gradients $(g_s)$ and hints $(h_s)$ (dual vectors), the **optimistic loss vector** used to compute $w_{t+1}$ is
--   $$
--   \ell_t=h_{t+1}+\sum_{s\in N_t}(g_s-h_s),
--   $$
--   the next hint plus the corrections from the gradients revealed at the end of round $t$.
-- source:
--   Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, Optimal Learning in Games with Arbitrary Delays: Best-of-Both-Worlds for Self-Play and Adversarial Opponents, STOC 2027 submission (manuscript sha256 d17ba8b0…1247), (MAO) p.9; Algorithm 1 line 5, p.12

import Mathlib
import Definitions.Def_DelayedGamesMAO_newObs

set_option autoImplicit false

namespace DelayedGamesMAO

/-- **The optimistic loss vector** `ℓ_t := h_{t+1} + ∑_{s∈N_t} (g_s − h_s)`.
Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, *Optimal Learning in Games with Arbitrary Delays:
Best-of-Both-Worlds for Self-Play and Adversarial Opponents*, STOC 2027 submission manuscript
(sha256 d17ba8b0…1247), (MAO) p.9, §6.1 p.13, and Algorithm 1 line 5, p.12.

`g s` is the gradient of round `s`, `h s` the hint of round `s` (dual vectors). -/
def optLoss {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (d : ℕ → ℕ)
    (g h : ℕ → E →L[ℝ] ℝ) (t : ℕ) : E →L[ℝ] ℝ :=
  h (t + 1) + ∑ s ∈ newObs d t, (g s - h s)

end DelayedGamesMAO


