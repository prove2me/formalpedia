-- Prove2me | Definitions.Def_ProxGapTight_Phi
-- name    : ProxGapTight_Phi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:44:48.054267+00:00
-- url     : https://prove2.me/theorems/8816d181-0284-4a15-88f8-7bad91ed68ea
-- title:
--   Amplification function $\Phi_t(u)=1-(1-u)^t$
-- statement:
--   For an integer $t$ and a real $u$,
--   $$
--   \Phi_t(u)=1-(1-u)^t.
--   $$
--
--   If a word has relative weight $u$ and $t$ of its coordinates are sampled independently and uniformly, $\Phi_t(u)$ is the probability that at least one sampled coordinate is nonzero. The construction amplifies all relative distances of a small-distance example through $u\mapsto\Phi_t(u)$.
--
--   **Formalization Note** $t$ is a natural number and the power is an ordinary integer power.
-- source:
--   Kominers, Thaler, Zheng, The One-and-a-Half Johnson Bound Is Tight for Proximity Gaps of General Linear Codes, manuscript (Sept. 2026; STOC 2027 submission; sha256 ac050071…), §2, p.6, display (recalled p.12)

import Mathlib

namespace ProxGapTight

/-- The **amplification function** `Φ_t(u) := 1 − (1 − u)^t`, Kominers, Thaler, Zheng, manuscript
(Sept. 2026), §2, p.6, display (recalled on p.12).

**Formalization Note.** `t` is a natural number and the power is the monoid power, as `t` is an
integer in every use (proof of Theorem 3.1, p.12: "an integer t ≥ 1"). -/
def Phi (t : ℕ) (u : ℝ) : ℝ := 1 - (1 - u) ^ t

end ProxGapTight


