-- Prove2me | Definitions.Def_IntroDelayAMDP_AlgState
-- name    : IntroDelayAMDP_AlgState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:44:18.592407+00:00
-- url     : https://prove2.me/theorems/e573f6ad-9600-4d30-9454-233457bd5f88
-- title:
--   The state of Algorithm 1 between episodes
-- statement:
--   Before an episode, the algorithm's state records: the cumulative received losses; the observed next states of each pair; the visit counts; the policy and trajectory of each past episode; and for each estimate key $(k,s,a)$ whether it was started, whether it is unfinished, its attempt count $\hat w_k(s,a)$, its piece $L_{k,h}/2$, and the indicators $I_{k,\kappa}(s,a)$ of p.29.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Algorithm 1, p.16; App. A, p.29

import Mathlib

namespace IntroDelayAMDP

/-- **The state of Algorithm 1 between episodes** (Algorithm 1, printed p.16, and App. A, printed
p.29, of Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530)). Before episode `κ` (0-based) it records:
- `cumG s a = ∑_{κ′<κ} g_{κ′}(s, a)`, the cumulative received losses (line 3);
- `obs s a`, the next states observed after the visits to `(s, a)`, in order (line 17, Eq. (16));
- `visits s a = N_κ(s, a)`, the number of visits to `(s, a)` before episode `κ`;
- `pol k` and `traj k`, the policy played and the trajectory of each past episode `k`;
- for each estimate key `(k, s, a)`: `started` (the estimate was started in episode `k`),
  `active` (it is unfinished), `w` (its number `ŵ_k(s, a)` of attempts so far) and `piece`
  (`L_{k,h}/2`, added to the received loss at every attempt);
- `ind k κ′ s a`: the indicator `I_{k,κ′}(s, a)` that the attempt of `(k, s, a)` in episode `κ′`
  succeeded or randomly stopped it (p.29). -/
structure AlgState (St A : Type) where
  cumG : St → A → ℝ
  obs : St → A → List St
  visits : St → A → ℕ
  pol : ℕ → St → A → ℝ
  traj : ℕ → ℕ → St × A
  started : ℕ → St → A → Prop
  active : ℕ → St → A → Prop
  w : ℕ → St → A → ℕ
  piece : ℕ → St → A → ℝ
  ind : ℕ → ℕ → St → A → Prop

end IntroDelayAMDP


