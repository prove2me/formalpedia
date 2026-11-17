-- Prove2me | Definitions.Def_IntroDelayAMDP_Supplement_alg5Policy
-- name    : IntroDelayAMDP_Supplement_alg5Policy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:52:43.696192+00:00
-- url     : https://prove2.me/theorems/c31b8b37-7913-46f3-91d2-b063fb3f7cf2
-- title:
--   Algorithm 5 — the policy played in episode $t$
-- statement:
--   The policy $\pi_t$ played by **Algorithm 5** in episode $t$: $\pi_t(a\mid s)\propto\exp(-\eta\sum_k(\hat Q_k-\eta\hat Q_k^2)(s,a))$ with the running estimates of the run before episode $t$, except that a given fixed policy is played in every episode when $\theta>1/2$ or $K<2\sqrt K$ (p.19, carried over to Algorithm 5 in the proof of Theorem 5.2, p.63).
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Algorithm 5, line 2, p.59; p.19

import Mathlib
import Definitions.Def_IntroDelayAMDP_expPolicy
import Definitions.Def_IntroDelayAMDP_Supplement_alg5Run

namespace IntroDelayAMDP.Supplement

open Classical in
/-- **The policy `π_t` played by Algorithm 5 in episode `t`** (line 2, printed p.59, PDF p.61, of
Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530): "let
`π_t(a | s) ∝ exp(−η ∑_{t′<t} g_{t′}(s, a))`"), for the 0-based episode `t`, on the sample path
`(traj, coin)`. As for Algorithm 3 (printed p.19: "If `θ > 1/2` or `K < 2√K`, the agent plays a fixed
policy"; Algorithm 5 inherits it, proof of Theorem 5.2, printed p.63), the agent plays the given fixed
policy `πfix` in every episode when `θ > 1/2` or `K < 2√K`. -/
noncomputable def alg5Policy {X A : Type} [Fintype A] {d H : ℕ} (L : LayeredSpace X H)
    (φ : X → A → Fin d → ℝ) (ℓ : ℕ → X → A → ℝ) (p : LinParams) (rule : RemovalRule d)
    (K sqrtK dbar : ℕ) (dl : ℕ → ℕ) (πfix : X → A → ℝ) (traj : ℕ → ℕ → X × A)
    (coin : ℕ → ℕ → ℕ → ℝ) (t : ℕ) : X → A → ℝ :=
  if 1 / 2 < p.theta ∨ K < 2 * sqrtK then πfix
  else
    let σ := alg5Run L φ ℓ p rule K sqrtK dbar dl traj coin t
    expPolicy p.eta (fun s a => ∑ k ∈ Finset.range K, (σ.qhat k s a - p.eta * σ.qhat k s a ^ 2))

end IntroDelayAMDP.Supplement


