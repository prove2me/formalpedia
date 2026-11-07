-- Prove2me | Definitions.Def_IntroDelayAMDP_sampleTraj
-- name    : IntroDelayAMDP_sampleTraj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:45:55.125435+00:00
-- url     : https://prove2.me/theorems/bc82cd70-8a36-4c12-bece-6280bfceec62
-- title:
--   A sampled trajectory
-- statement:
--   The sequence $(s_h,a_h)_h$ of state-action pairs of a trajectory, with $a_h$ sampled from $\pi(\cdot\mid s_h)$. Only $h<H$ is used. This is line 7 of Algorithm 1.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Algorithm 1, line 7, p.16

import Mathlib
import Definitions.Def_IntroDelayAMDP_LayeredSpace
import Definitions.Def_IntroDelayAMDP_sampleCat
import Definitions.Def_IntroDelayAMDP_sampleStates

namespace IntroDelayAMDP

/-- **A sampled trajectory** `(s_{κ,h}, a_{κ,h})_{h=0}^{H−1}` (Algorithm 1, line 7, printed p.16, of
Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530): "Execute `π_κ`, and observe the trajectory"). `sampleTraj … h = (s_h, a_h)` with the states
of `sampleStates` and `a_h = sampleCat a₀ (π s_h) (act h)`. Only `h < H` is used. -/
noncomputable def sampleTraj {St A : Type} [Fintype St] [Fintype A] {H : ℕ}
    (L : LayeredSpace St H) (P : St → A → St → ℝ) (π : St → A → ℝ) (act nxt : ℕ → ℝ) (a0 : A)
    (h : ℕ) : St × A :=
  (sampleStates L P π act nxt a0 h,
    sampleCat a0 (π (sampleStates L P π act nxt a0 h)) (act h))

end IntroDelayAMDP


