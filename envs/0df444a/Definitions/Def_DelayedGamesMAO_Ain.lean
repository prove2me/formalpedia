-- Prove2me | Definitions.Def_DelayedGamesMAO_Ain
-- name    : DelayedGamesMAO_Ain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:23:42.971814+00:00
-- url     : https://prove2.me/theorems/45f5c5fe-a682-413d-b288-500fc3461e36
-- title:
--   Total incoming weight $A^{\mathrm{in}}_t=\sum_{k=0}^{t-1}c^{(t)}_k$
-- statement:
--   For an array of anchor weights $(c^{(t)}_k)$, where $c^{(t)}_k$ is the weight on anchor $w_k$ in the update computing $w_t$, the **total incoming weight** of $w_t$ is
--   $$
--   A^{\mathrm{in}}_t=\sum_{k=0}^{t-1}c^{(t)}_k ,
--   $$
--   with the empty sum ($t=0$) equal to $0$.
-- source:
--   Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, Optimal Learning in Games with Arbitrary Delays: Best-of-Both-Worlds for Self-Play and Adversarial Opponents, STOC 2027 submission (manuscript sha256 d17ba8b0…1247), §5.1, p.10; Proposition 2, p.14

import Mathlib

set_option autoImplicit false

namespace DelayedGamesMAO

/-- **Total incoming weight** `A_t^{in} := ∑_{k=0}^{t−1} c_k^{(t)}` of an anchor-weight array.
Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, *Optimal Learning in Games with Arbitrary Delays:
Best-of-Both-Worlds for Self-Play and Adversarial Opponents*, STOC 2027 submission manuscript
(sha256 d17ba8b0…1247), §5.1, p.10, and Proposition 2, p.14 ("with empty sums equal to zero").

`c t k` is `c_k^{(t)}`: the weight on anchor `w_k` in the update computing `w_t`. -/
def Ain (c : ℕ → ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑ k ∈ Finset.range t, c t k

end DelayedGamesMAO


