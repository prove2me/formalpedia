-- Prove2me | Definitions.Def_IntroDelayAMDP_expPolicy
-- name    : IntroDelayAMDP_expPolicy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:43:21.754199+00:00
-- url     : https://prove2.me/theorems/169edd13-ffe2-4418-9236-3b00bc19dc89
-- title:
--   Exponential-weights policy
-- statement:
--   For a learning rate $\eta$ and cumulative received losses $G(s,a)=\sum_{\kappa'<\kappa}g_{\kappa'}(s,a)$,
--   $$\pi(a\mid s)=\frac{\exp(-\eta G(s,a))}{\sum_{a'}\exp(-\eta G(s,a'))}$$
--   at every state. This is line 3 of Algorithm 1.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Algorithm 1, line 3, p.16

import Mathlib

namespace IntroDelayAMDP

/-- **Exponential-weights policy** (Algorithm 1, line 3, p.16). Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), printed p.16: "For every
state `s`, let `π_κ(a | s) ∝ exp(−η ∑_{κ′<κ} g_{κ′}(s, a))`."

For a learning rate `η` and the cumulative received losses `G(s, a) = ∑_{κ′<κ} g_{κ′}(s, a)`,
`expPolicy η G s a = exp(−η G(s, a)) / ∑_{a′} exp(−η G(s, a′))`, at every state. -/
noncomputable def expPolicy {St A : Type} [Fintype A] (η : ℝ) (G : St → A → ℝ) (s : St) (a : A) : ℝ :=
  Real.exp (-η * G s a) / ∑ a', Real.exp (-η * G s a')

end IntroDelayAMDP


