-- Prove2me | Definitions.Def_DelayedGamesMAO_sigmaMax
-- name    : DelayedGamesMAO_sigmaMax
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:25:43.36243+00:00
-- url     : https://prove2.me/theorems/7090f054-c51d-463c-8961-dcc7dd6a8b63
-- title:
--   Maximum number of pending rounds $\sigma_{\max}=\max_{t\in[T]}\sigma_t$
-- statement:
--   For a delay sequence $(d_s)$ and a horizon $T$, the **maximum number of pending rounds** is
--   $$
--   \sigma_{\max}=\max_{t\in[T]}\sigma_t ,
--   $$
--   the largest number of earlier rounds whose feedback is missing at any time.
--
--   **Formalization Note** The maximum is the supremum of a finite set of naturals.
-- source:
--   Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, Optimal Learning in Games with Arbitrary Delays: Best-of-Both-Worlds for Self-Play and Adversarial Opponents, STOC 2027 submission (manuscript sha256 d17ba8b0…1247), §2, Delay-induced notation, p.3

import Mathlib
import Definitions.Def_DelayedGamesMAO_sigma

set_option autoImplicit false

namespace DelayedGamesMAO

/-- **Maximum number of pending rounds** `σ_max := max_{t ∈ [T]} σ_t`.
Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, *Optimal Learning in Games with Arbitrary Delays:
Best-of-Both-Worlds for Self-Play and Adversarial Opponents*, STOC 2027 submission manuscript
(sha256 d17ba8b0…1247), §2 "Delay-induced notation", p.3.

**Formalization Note.** The maximum over `[T] = Finset.Icc 1 T` is `Finset.sup` in `ℕ`; for
`T ≥ 1` it is the attained maximum. -/
def sigmaMax (d : ℕ → ℕ) (T : ℕ) : ℕ :=
  (Finset.Icc 1 T).sup (sigma d)

end DelayedGamesMAO


