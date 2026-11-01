-- Prove2me | Definitions.Def_RecoveringBandits_schedReward
-- name    : RecoveringBandits_schedReward
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:53:29.671895+00:00
-- url     : https://prove2.me/theorems/467dcf2d-3580-42ad-843f-19c907309211
-- title:
--   Reward of a single-arm schedule (last pull at time 0)
-- statement:
--   A schedule of one arm up to a horizon $T$ is a finite set of pull times $0<s_1<\dots<s_J\le T$; by convention the arm was last pulled at time $s_0=0$, right before the start. With recovery function $r$, the schedule earns
--
--   $$\sum_{j=1}^{J} r(s_j-s_{j-1}).$$
--
--   The **previous pull** of $s$ in a set $S$ is the largest element of $S$ below $s$, or $0$ if there is none. This is the inner sum of the objective of the offline problem (1) and of problem (2).
--
--   **Formalization Note** The schedule is the finite set $S=\{s_1,\dots,s_J\}$, and the gap before $s\in S$ is $s-\operatorname{prev}_S(s)\ge 1$.
-- source:
--   Simchi-Levi–Zheng–Zhu, Offline Planning and Online Learning under Recovering Rewards, arXiv:2106.14813v2, §2, p.6 (initialization at time 0); §3.1, (1), pp.7–8; §4.1, (2), p.11

import Mathlib

namespace RecoveringBandits

/-- **The previous pull time.** For a finite set `S` of pull times and a time `s`, the largest
element of `S` strictly below `s`, or `0` if there is none: the arm was last pulled at time `0`
before the horizon starts (arXiv:2106.14813v2, §2, p.6: "the last time that each arm is pulled is
time period 0, right before the start of the problem at time period 1"). -/
def prevPull (S : Finset ℕ) (s : ℕ) : ℕ :=
  (S.filter (· < s)).sup id

/-- **The reward of a single-arm schedule.** For a recovery function `r` and a finite set `S ⊆ [1, T]`
of pull times `s_1 < ⋯ < s_J`, the total mean reward `∑_{j=1}^J r(s_j − s_{j−1})` with `s_0 = 0`:
the inner sum of the objective of the offline problem (1) (arXiv:2106.14813v2, §3.1, (1),
pp.7–8) and of problem (2) (§4.1, p.11).

**Formalization Note.** A schedule `0 = s_0 < s_1 < ⋯ < s_J ≤ T` is encoded by the finite set
`{s_1, …, s_J}`; the gap before `s_j` is `s_j − prevPull S s_j`, and the first gap is measured from
time `0`. Each term `s − prevPull S s` is a positive natural number for `s ∈ S`, so the truncated
subtraction never truncates. -/
def schedReward (r : ℕ → ℝ) (S : Finset ℕ) : ℝ :=
  ∑ s ∈ S, r (s - prevPull S s)

end RecoveringBandits


