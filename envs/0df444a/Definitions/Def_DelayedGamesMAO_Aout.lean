-- Prove2me | Definitions.Def_DelayedGamesMAO_Aout
-- name    : DelayedGamesMAO_Aout
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:23:45.263772+00:00
-- url     : https://prove2.me/theorems/5fc0848f-0d0d-4c0e-9c3b-5c51ff38860d
-- title:
--   Total outgoing weight $A^{\mathrm{out}}_t=\sum_{k=t}^{T}c^{(k+1)}_t$
-- statement:
--   For an array of anchor weights $(c^{(t)}_k)$ and a horizon $T$, the **total outgoing weight** of $w_t$ is
--   $$
--   A^{\mathrm{out}}_t=\sum_{k=t}^{T}c^{(k+1)}_t ,
--   $$
--   the total weight $w_t$ receives as an anchor in later updates; the empty sum ($t=T+1$) is $0$.
-- source:
--   Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, Optimal Learning in Games with Arbitrary Delays: Best-of-Both-Worlds for Self-Play and Adversarial Opponents, STOC 2027 submission (manuscript sha256 d17ba8b0…1247), §5.1, p.10; Proposition 2, p.14

import Mathlib

set_option autoImplicit false

namespace DelayedGamesMAO

/-- **Total outgoing weight** `A_t^{out} := ∑_{k=t}^{T} c_t^{(k+1)}` of an anchor-weight array.
Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, *Optimal Learning in Games with Arbitrary Delays:
Best-of-Both-Worlds for Self-Play and Adversarial Opponents*, STOC 2027 submission manuscript
(sha256 d17ba8b0…1247), §5.1, p.10, and Proposition 2, p.14 ("with empty sums equal to zero").

`c k t` is `c_t^{(k)}`: the weight on anchor `w_t` in the update computing `w_k`. -/
def Aout (c : ℕ → ℕ → ℝ) (T t : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc t T, c (k + 1) t

end DelayedGamesMAO


