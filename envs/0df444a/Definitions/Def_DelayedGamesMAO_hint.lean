-- Prove2me | Definitions.Def_DelayedGamesMAO_hint
-- name    : DelayedGamesMAO_hint
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:25:55.034697+00:00
-- url     : https://prove2.me/theorems/2913b02a-2d82-46e2-9a74-a174cd8ec6b9
-- title:
--   Hints $h_t=g_{s_t}$, with $g_0=0$ and $h_{T+1}=0$
-- statement:
--   Given a horizon $T$, a delay sequence and gradients $g_1,g_2,\dots$ (dual vectors), the **hint** of round $t$ is
--   $$
--   h_t=g_{s_t}\quad(1\le t\le T),\qquad g_0:=0,\qquad h_{T+1}:=0,
--   $$
--   where $s_t$ is the hint source. In particular $h_t=0$ whenever $s_t=0$, and $h_1=0$.
--
--   **Formalization Note** The convention $g_0=0$ is built in, whatever value the gradient sequence has at index $0$; the hint is $0$ for every $t>T$ (only $t=T+1$ is used).
-- source:
--   Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, Optimal Learning in Games with Arbitrary Delays: Best-of-Both-Worlds for Self-Play and Adversarial Opponents, STOC 2027 submission (manuscript sha256 d17ba8b0…1247), §3, p.5, and Algorithm 1, p.12

import Mathlib
import Definitions.Def_DelayedGamesMAO_hintSrc

set_option autoImplicit false

namespace DelayedGamesMAO

/-- **Hints** `h_t := g_{s_t}` of MAO-OMD, with `g_0 := 0` and `h_{T+1} := 0`.
Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, *Optimal Learning in Games with Arbitrary Delays:
Best-of-Both-Worlds for Self-Play and Adversarial Opponents*, STOC 2027 submission manuscript
(sha256 d17ba8b0…1247), §3, p.5 ("set `h_t := g_{s_t}`, where `g_0 := 0`"), and Algorithm 1, p.12
("`h_1 = 0`", line 3: "`h_{t+1} = g_{s_{t+1}}` (0 if `t = T`)").

`g t` is the gradient of round `t` (an element of the dual space, so `‖·‖` is the dual norm).

**Formalization Note.** `h_t = 0` when `s_t = 0` (the convention `g_0 = 0`, whatever the
value `g 0` of the given sequence) and for `t > T` (only `h_{T+1}` is read). Since
`s_1 = 0`, `h_1 = 0`. -/
def hint {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (d : ℕ → ℕ) (T : ℕ)
    (g : ℕ → E →L[ℝ] ℝ) (t : ℕ) : E →L[ℝ] ℝ :=
  if hintSrc d t = 0 ∨ T < t then 0 else g (hintSrc d t)

end DelayedGamesMAO


