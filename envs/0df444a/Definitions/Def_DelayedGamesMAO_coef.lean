-- Prove2me | Definitions.Def_DelayedGamesMAO_coef
-- name    : DelayedGamesMAO_coef
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:30:03.253398+00:00
-- url     : https://prove2.me/theorems/c7238d50-ae9c-4134-9b96-7c9b8d031d9c
-- title:
--   The anchor coefficients (8) $c^{(t+1)}_s$
-- statement:
--   Given a delay sequence, $\gamma>0$, learning rates $\eta$ and an allocation schedule $\alpha$, the **anchor coefficients** of the update computing $w_{t+1}$ are, for $0\le s\le t$,
--   $$
--   c^{(t+1)}_0=\beta_{t+1}-\beta_t,\qquad
--   c^{(t+1)}_s=b_t\,\mathbb 1\{s=t\}+r^{(t)}_s-r^{(t+1)}_s\quad(s\in[t]).
--   $$
--   The weight released by each anchor is passed on to $w_{t+1}$, the remainder $b_t$ goes to $w_t$, and the increment of $\beta$ is injected through the reference point $w_0$.
--
--   **Formalization Note** The array is indexed superscript first: the definition's value at $(t,s)$ is $c^{(t)}_s$, read for $1\le t\le T+1$ and $0\le s<t$; its value at $t=0$ is never read.
-- source:
--   Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, Optimal Learning in Games with Arbitrary Delays: Best-of-Both-Worlds for Self-Play and Adversarial Opponents, STOC 2027 submission (manuscript sha256 d17ba8b0…1247), §5.1, eq. (8), p.11

import Mathlib
import Definitions.Def_DelayedGamesMAO_remainder

set_option autoImplicit false

namespace DelayedGamesMAO

/-- **The anchor coefficients** (8) of MAO-OMD.
Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, *Optimal Learning in Games with Arbitrary Delays:
Best-of-Both-Worlds for Self-Play and Adversarial Opponents*, STOC 2027 submission manuscript
(sha256 d17ba8b0…1247), §5.1, eq. (8), p.11:
`c_0^{(t+1)} := β_{t+1} − β_t`, `c_s^{(t+1)} := (β_t − ∑_{k∈A_t} r_k^{(t)}) I{s = t} + r_s^{(t)} − r_s^{(t+1)}`
for all `s ∈ [t]`.

`coef d γ η α t s` is `c_s^{(t)}` (superscript first); the paper uses it for `0 ≤ s < t`,
`1 ≤ t ≤ T + 1`. With `t = t' + 1`: `c_0^{(t'+1)} = β_{t'+1} − β_{t'}` and, for `1 ≤ s ≤ t'`,
`c_s^{(t'+1)} = b_{t'} 𝟙{s = t'} + r_s^{(t')} − r_s^{(t'+1)}`.

**Formalization Note.** Total in `t, s`; the value at `t = 0` is never read. -/
noncomputable def coef (d : ℕ → ℕ) (γ : ℝ) (η : ℕ → ℝ) (α : ℕ → ℕ → ℝ) (t s : ℕ) : ℝ :=
  if s = 0 then beta d γ η t - beta d γ η (t - 1)
  else (if s = t - 1 then remainder d γ η α (t - 1) else 0) +
    remWeight d γ η α (t - 1) s - remWeight d γ η α t s

end DelayedGamesMAO


