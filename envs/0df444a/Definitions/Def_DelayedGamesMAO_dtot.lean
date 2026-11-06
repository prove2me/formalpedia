-- Prove2me | Definitions.Def_DelayedGamesMAO_dtot
-- name    : DelayedGamesMAO_dtot
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:23:40.876591+00:00
-- url     : https://prove2.me/theorems/660b6a3e-d6b1-4532-90e8-af2baa889451
-- title:
--   Total delay $d_{\mathrm{tot}}=\sum_{t\in[T]}d_t$
-- statement:
--   For a delay sequence $(d_t)$ and a horizon $T$, the **total delay** is
--   $$
--   d_{\mathrm{tot}}=\sum_{t=1}^T d_t .
--   $$
--   The adversarial guarantee of MAO-OMD is $O(\sqrt{T+d_{\mathrm{tot}}})$.
-- source:
--   Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, Optimal Learning in Games with Arbitrary Delays: Best-of-Both-Worlds for Self-Play and Adversarial Opponents, STOC 2027 submission (manuscript sha256 d17ba8b0…1247), §2, Delay-induced notation, p.3

import Mathlib

set_option autoImplicit false

namespace DelayedGamesMAO

/-- **Total delay** `d_tot := ∑_{t ∈ [T]} d_t`.
Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, *Optimal Learning in Games with Arbitrary Delays:
Best-of-Both-Worlds for Self-Play and Adversarial Opponents*, STOC 2027 submission manuscript
(sha256 d17ba8b0…1247), §2 "Delay-induced notation", p.3. -/
def dtot (d : ℕ → ℕ) (T : ℕ) : ℕ :=
  ∑ t ∈ Finset.Icc 1 T, d t

end DelayedGamesMAO


