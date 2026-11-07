-- Prove2me | Definitions.Def_IntroDelayAMDP_EpisodeCoins
-- name    : IntroDelayAMDP_EpisodeCoins
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:44:01.590021+00:00
-- url     : https://prove2.me/theorems/ce0123a0-5923-41cb-b9fe-1611ca53efe6
-- title:
--   The uniform coins of one episode
-- statement:
--   The numbers read in one episode: the action draw and next-state draw of each layer (line 7 of Algorithm 1), and for each estimate $(k,s,a)$ its acceptance coin (line 10) and random-stop coin (line 12).
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Algorithm 1, p.16

import Mathlib

namespace IntroDelayAMDP

/-- **The uniform coins of one episode** (Algorithm 1, printed p.16, of Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530)): `act h` and
`nxt h` for the action at layer `h` and the next state after layer `h` (line 7); `acc k s a` and
`stop k s a` for the acceptance (line 10) and the random stop (line 12) of the attempt of the
estimate `(k, s, a)` in this episode. -/
structure EpisodeCoins (St A : Type) where
  /-- action draw at layer `h` -/
  act : ℕ → ℝ
  /-- next-state draw after layer `h` -/
  nxt : ℕ → ℝ
  /-- acceptance coin of the estimate `(k, s, a)` -/
  acc : ℕ → St → A → ℝ
  /-- random-stop coin of the estimate `(k, s, a)` -/
  stop : ℕ → St → A → ℝ

end IntroDelayAMDP


