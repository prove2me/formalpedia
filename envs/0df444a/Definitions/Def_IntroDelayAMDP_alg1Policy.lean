-- Prove2me | Definitions.Def_IntroDelayAMDP_alg1Policy
-- name    : IntroDelayAMDP_alg1Policy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:51:32.787292+00:00
-- url     : https://prove2.me/theorems/a77f91c1-c14f-402a-a381-b1f2cd169006
-- title:
--   The policy played by Algorithm 1
-- statement:
--   $\pi_k$ on a sample point: the exponential-weights policy of the cumulative received losses before episode $k$.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Algorithm 1, line 3, p.16

import Mathlib
import Definitions.Def_IntroDelayAMDP_runState
import Definitions.Def_IntroDelayAMDP_expPolicy

namespace IntroDelayAMDP

/-- **The policy `π_k` played by Algorithm 1 in episode `k`** (line 3, printed p.16, of Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530):
"For every state `s`, let `π_κ(a | s) ∝ exp(−η ∑_{κ′<κ} g_{κ′}(s, a))`"), on the sample point `ω`, for
the 0-based episode `k`. -/
noncomputable def alg1Policy {St A : Type} [Fintype St] [DecidableEq St] [Fintype A] [Nonempty A] {H K : ℕ}
    (L : LayeredSpace St H) (P : St → A → St → ℝ) (ℓ : ℕ → St → A → ℝ) (p : AlgParams)
    (ω : Tape St A K H) (k : ℕ) : St → A → ℝ :=
  expPolicy p.eta (runState L P ℓ p ω k).cumG

end IntroDelayAMDP


