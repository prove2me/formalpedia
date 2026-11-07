-- Prove2me | Definitions.Def_IntroDelayAMDP_valueIter
-- name    : IntroDelayAMDP_valueIter
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:42:58.23042+00:00
-- url     : https://prove2.me/theorems/276ca518-3143-4649-a140-381dea08b268
-- title:
--   Backward value iteration
-- statement:
--   For a transition $P$, a per-pair cost $c$ and a policy $\pi$, the $n$-step value is defined by $U_0\equiv 0$ and
--   $$U_{n+1}(s)=\sum_a\pi(a\mid s)\Bigl(c(s,a)+\sum_{s'}P(s'\mid s,a)U_n(s')\Bigr).$$
--
--   This is the recursion behind the Bellman equations (12).
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Eq. (12), p.13

import Mathlib

namespace IntroDelayAMDP

/-- **Backward value iteration** (auxiliary for Eq. (12), p.13). Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), printed p.13, Eq. (12).

`valueIter P c π n s` is the expected cost collected in `n` steps from state `s` when actions are
drawn from `π(· | s)`, the cost of pair `(s, a)` is `c s a` and the next state is drawn from
`P(· | s, a)`: `valueIter … 0 = 0` and
`valueIter … (n+1) s = ∑ₐ π(a|s) (c(s,a) + ∑_{s'} P(s'|s,a) valueIter … n s')`. -/
noncomputable def valueIter {St A : Type} [Fintype St] [Fintype A] (P : St → A → St → ℝ)
    (c : St → A → ℝ) (π : St → A → ℝ) : ℕ → St → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun s => ∑ a, π s a * (c s a + ∑ s', P s a s' * valueIter P c π n s')

end IntroDelayAMDP


