-- Prove2me | Definitions.Def_IntroDelayAMDP_Supplement_alg4Policy
-- name    : IntroDelayAMDP_Supplement_alg4Policy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:44:36.182717+00:00
-- url     : https://prove2.me/theorems/93aefaf8-86d6-4aeb-b972-05223ffd8f7f
-- title:
--   Algorithm 4 — the policy played in episode $t$
-- statement:
--   The policy $\pi_t$ played by **Algorithm 4** in episode $t$ on the sample point $\omega$:
--   $$\pi_t(a\mid s)=\frac{\exp\bigl(-\eta\sum_{t'<t}g_{t'}(s,a)\bigr)}{\sum_{a'}\exp\bigl(-\eta\sum_{t'<t}g_{t'}(s,a')\bigr)},$$
--   where $\sum_{t'<t}g_{t'}$ is the cumulative received loss of the run before episode $t$. These are the policies $\pi_k$ whose regret Theorem 5.1 bounds.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Algorithm 4, line 2, p.58

import Mathlib
import Definitions.Def_IntroDelayAMDP_expPolicy
import Definitions.Def_IntroDelayAMDP_Supplement_alg4Run

namespace IntroDelayAMDP.Supplement

/-- **The policy `π_t` played by Algorithm 4 in episode `t`** (line 2, printed p.58, PDF p.60, of
Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530): "For every state `s`, let
`π_t(a | s) ∝ exp(−η ∑_{t′<t} g_{t′}(s, a))`"), on the sample point `ω`, for the 0-based episode `t`. -/
noncomputable def alg4Policy {St A : Type} [Fintype St] [DecidableEq St] [Fintype A] [Nonempty A]
    {H K : ℕ} (L : LayeredSpace St H) (P : St → A → St → ℝ) (ℓ : ℕ → St → A → ℝ) (p : AlgParams)
    (dbar : ℕ) (dl : ℕ → ℕ) (ω : Tape St A K H) (t : ℕ) : St → A → ℝ :=
  expPolicy p.eta (alg4Run L P ℓ p dbar dl ω t).cumG

end IntroDelayAMDP.Supplement


