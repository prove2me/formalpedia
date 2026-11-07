-- Prove2me | Definitions.Def_IntroDelayAMDP_occIter
-- name    : IntroDelayAMDP_occIter
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:42:58.830186+00:00
-- url     : https://prove2.me/theorems/9beb49a7-ceba-4a20-b772-cd15f722fb12
-- title:
--   Forward state distribution
-- statement:
--   $\mu_n(s)$ is the probability that a trajectory started at $s_0$, with actions from $\pi$ and next states from $P'$, is at $s$ at step $n$: $\mu_0(s)=\mathbf 1[s=s_0]$ and
--   $$\mu_{n+1}(s')=\sum_{s,a}\mu_n(s)\,\pi(a\mid s)\,P'(s'\mid s,a).$$
--
--   It is the recursion behind the occupancy measure (13).
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Eq. (13), p.13

import Mathlib

namespace IntroDelayAMDP

/-- **Forward state distribution** (auxiliary for Eq. (13), p.13). Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), printed p.13, Eq. (13).

`occIter P π s0 n s` is the probability that a trajectory started at `s0`, with actions drawn
from `π(· | s)` and next states from `P(· | s, a)`, is at state `s` at step `n`:
`occIter … 0 s = 1[s = s0]` and
`occIter … (n+1) s' = ∑_{s,a} occIter … n s · π(a | s) · P(s' | s, a)`. -/
noncomputable def occIter {St A : Type} [Fintype St] [DecidableEq St] [Fintype A]
    (P : St → A → St → ℝ) (π : St → A → ℝ) (s0 : St) : ℕ → St → ℝ
  | 0 => fun s => if s = s0 then 1 else 0
  | n + 1 => fun s' => ∑ s, ∑ a, occIter P π s0 n s * π s a * P s a s'

end IntroDelayAMDP


