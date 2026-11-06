-- Prove2me | Definitions.Def_DelayedGamesMAO_congAlloc
-- name    : DelayedGamesMAO_congAlloc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:27:33.471631+00:00
-- url     : https://prove2.me/theorems/47b22d62-cf2e-4b6c-82ec-7be5eec29356
-- title:
--   The congestion schedule (10) $\alpha^{(t)}_s=\mathbb 1\{s\in A_t\}/\kappa_{s,t}$
-- statement:
--   For a delay sequence, the **congestion allocation schedule** is
--   $$
--   \alpha^{(t)}_s=\frac{\mathbb 1\{s\in A_t\}}{\kappa_{s,t}} ,
--   $$
--   where $\kappa_{s,t}$ is the running congestion. It is the schedule with which MAO-OMD attains its guarantees.
--
--   **Formalization Note** The paper prints (10) for $1\le s\le t\le T$; Definition 1 and Lemma 6 use the array up to $t=T+1$, where the same formula gives $\alpha^{(T+1)}_s=0$ for $s\le T$ when every feedback arrives by the end of round $T$. For $s\in A_t$, $\kappa_{s,t}\ge q_t\ge1$, so the division is never by zero.
-- source:
--   Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, Optimal Learning in Games with Arbitrary Delays: Best-of-Both-Worlds for Self-Play and Adversarial Opponents, STOC 2027 submission (manuscript sha256 d17ba8b0…1247), §5.1, eq. (10), p.12

import Mathlib
import Definitions.Def_DelayedGamesMAO_active
import Definitions.Def_DelayedGamesMAO_kappaRun

set_option autoImplicit false

namespace DelayedGamesMAO

/-- **The congestion allocation schedule** (10): `α_s^{(t)} := 𝟙{s ∈ A_t} / κ_{s,t}`.
Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, *Optimal Learning in Games with Arbitrary Delays:
Best-of-Both-Worlds for Self-Play and Adversarial Opponents*, STOC 2027 submission manuscript
(sha256 d17ba8b0…1247), §5.1, eq. (10), p.12.

`congAlloc d t s` is `α_s^{(t)}`.

**Formalization Note.** The paper prints (10) for `1 ≤ s ≤ t ≤ T`, while Definition 1 and
Lemma 6 use the array up to `t = T + 1`; the same formula is used there, and it gives
`α_s^{(T+1)} = 0` for `s ≤ T` because no round `s ≤ T` is active at `T + 1` when every
feedback arrives by the end of round `T`. When `s ∈ A_t`, `κ_{s,t} ≥ q_t ≥ 1`, so the division
is never by `0`. -/
noncomputable def congAlloc (d : ℕ → ℕ) (t s : ℕ) : ℝ :=
  if s ∈ active d t then 1 / (kappaRun d s t : ℝ) else 0

end DelayedGamesMAO


