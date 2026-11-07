-- Prove2me | Definitions.Def_IntroDelayAMDP_sampleStates
-- name    : IntroDelayAMDP_sampleStates
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:44:52.504118+00:00
-- url     : https://prove2.me/theorems/7e85d61e-d382-4413-b5fb-27874f927377
-- title:
--   The states of a sampled trajectory
-- statement:
--   With action draws and next-state draws, $s_0$ is the initial state, $a_h$ is sampled from $\pi(\cdot\mid s_h)$ and $s_{h+1}$ from $P(\cdot\mid s_h,a_h)$, each by the inverse-CDF sampler.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Section 2.1, p.12

import Mathlib
import Definitions.Def_IntroDelayAMDP_LayeredSpace
import Definitions.Def_IntroDelayAMDP_sampleCat

namespace IntroDelayAMDP

/-- **The states of a sampled trajectory** (Section 2.1, printed p.12, of Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530): "the agent
starts from the initial state `s_{k,0} = s₀`. At every step `h` … chooses an action `a_{k,h}` …
and then transitions to a new state `s_{k,h+1}` that is independently sampled from
`P(· | s_{k,h}, a_{k,h})`").

With the action draws `act h` and next-state draws `nxt h`, `sampleStates L P π act nxt a₀ h` is
`s_h`: `s_0 = s₀`, `a_h = sampleCat a₀ (π s_h) (act h)`, `s_{h+1} = sampleCat s_h (P s_h a_h) (nxt h)`. -/
noncomputable def sampleStates {St A : Type} [Fintype St] [Fintype A] {H : ℕ}
    (L : LayeredSpace St H) (P : St → A → St → ℝ) (π : St → A → ℝ) (act nxt : ℕ → ℝ) (a0 : A) :
    ℕ → St
  | 0 => L.s0
  | h + 1 =>
      sampleCat (sampleStates L P π act nxt a0 h)
        (P (sampleStates L P π act nxt a0 h)
          (sampleCat a0 (π (sampleStates L P π act nxt a0 h)) (act h))) (nxt h)

end IntroDelayAMDP


