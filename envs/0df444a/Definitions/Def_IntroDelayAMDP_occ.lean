-- Prove2me | Definitions.Def_IntroDelayAMDP_occ
-- name    : IntroDelayAMDP_occ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:45:17.991053+00:00
-- url     : https://prove2.me/theorems/f085878f-cc13-4c64-abf4-0776237da35b
-- title:
--   State-action occupancy measure, Eq. (13)
-- statement:
--   $q^{P',\pi}(s,a)=q^{P',\pi}(s)\,\pi(a\mid s)$ is the probability that a trajectory of $\pi$ under $P'$ visits the pair $(s,a)$.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Eq. (13), p.13

import Mathlib
import Definitions.Def_IntroDelayAMDP_LayeredSpace
import Definitions.Def_IntroDelayAMDP_occS

namespace IntroDelayAMDP

/-- **State-action occupancy measure** `q^{P′,π}(s, a)` (Eq. (13), p.13). Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), printed p.13:
"Since the action at `s` is drawn from `π(· | s)`, we have `q^{P′,π}(s, a) = q^{P′,π}(s) π(a | s)`".

`occ L P' π s a = occS L P' π s · π(a | s)` is the probability that a trajectory of `π` under `P'`
visits the pair `(s, a)`. -/
noncomputable def occ {St A : Type} [Fintype St] [DecidableEq St] [Fintype A] {H : ℕ}
    (L : LayeredSpace St H) (P' : St → A → St → ℝ) (π : St → A → ℝ) (s : St) (a : A) : ℝ :=
  occS L P' π s * π s a

end IntroDelayAMDP


