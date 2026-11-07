-- Prove2me | Definitions.Def_IntroDelayAMDP_alg1Traj
-- name    : IntroDelayAMDP_alg1Traj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:52:36.060962+00:00
-- url     : https://prove2.me/theorems/ae8ffe8f-e5e3-42cd-b253-7c243cccc478
-- title:
--   The trajectory of an episode
-- statement:
--   $\tau_k=(s_{k,h},a_{k,h})_{h}$ on a sample point: the trajectory sampled with the coins of episode $k$ under $\pi_k$ and the true transition.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Algorithm 1, line 7, p.16

import Mathlib
import Definitions.Def_IntroDelayAMDP_alg1Policy
import Definitions.Def_IntroDelayAMDP_sampleTraj

namespace IntroDelayAMDP

/-- **The trajectory `τ_k = (s_{k,h}, a_{k,h})_{h=0}^{H−1}` of episode `k`** (line 7, printed p.16, of
Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530)): the trajectory sampled with the coins of the 0-based episode `k` under `π_k` and the true
transition `P` (the same trajectory as inside `algStep`). -/
noncomputable def alg1Traj {St A : Type} [Fintype St] [DecidableEq St] [Fintype A] [Nonempty A] {H K : ℕ}
    (L : LayeredSpace St H) (P : St → A → St → ℝ) (ℓ : ℕ → St → A → ℝ) (p : AlgParams)
    (ω : Tape St A K H) (k : ℕ) : ℕ → St × A :=
  sampleTraj L P (alg1Policy L P ℓ p ω k) (coins ω k).act (coins ω k).nxt (Classical.arbitrary A)

end IntroDelayAMDP


