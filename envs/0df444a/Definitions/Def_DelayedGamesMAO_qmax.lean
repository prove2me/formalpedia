-- Prove2me | Definitions.Def_DelayedGamesMAO_qmax
-- name    : DelayedGamesMAO_qmax
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:26:42.553933+00:00
-- url     : https://prove2.me/theorems/ecf723fa-a31f-4813-b0f2-8a272cf2f45c
-- title:
--   Maximum number of active rounds $q_{\max}=\max_{t\in[T]}q_t$
-- statement:
--   For a delay sequence $(d_s)$ and a horizon $T$, the **maximum number of active rounds** is
--   $$
--   q_{\max}=\max_{t\in[T]}q_t .
--   $$
--   It equals $\sigma_{\max}+1$, and it is the quantity in which the self-play guarantees of MAO-OMD are stated.
--
--   **Formalization Note** The maximum is the supremum of a finite set of naturals (it is $0$ only for $T=0$, which the paper excludes).
-- source:
--   Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, Optimal Learning in Games with Arbitrary Delays: Best-of-Both-Worlds for Self-Play and Adversarial Opponents, STOC 2027 submission (manuscript sha256 d17ba8b0…1247), §2, Delay-induced notation, p.3

import Mathlib
import Definitions.Def_DelayedGamesMAO_q

set_option autoImplicit false

namespace DelayedGamesMAO

/-- **Maximum number of active rounds** `q_max := max_{t ∈ [T]} q_t`.
Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, *Optimal Learning in Games with Arbitrary Delays:
Best-of-Both-Worlds for Self-Play and Adversarial Opponents*, STOC 2027 submission manuscript
(sha256 d17ba8b0…1247), §2 "Delay-induced notation", p.3.

**Formalization Note.** The maximum over `[T] = Finset.Icc 1 T` is `Finset.sup` in `ℕ`; for
`T ≥ 1` (the paper's `T ∈ ℕ₊`) it is the attained maximum. -/
def qmax (d : ℕ → ℕ) (T : ℕ) : ℕ :=
  (Finset.Icc 1 T).sup (q d)

end DelayedGamesMAO


