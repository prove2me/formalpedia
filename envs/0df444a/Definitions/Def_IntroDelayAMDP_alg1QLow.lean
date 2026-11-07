-- Prove2me | Definitions.Def_IntroDelayAMDP_alg1QLow
-- name    : IntroDelayAMDP_alg1QLow
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:53:07.422203+00:00
-- url     : https://prove2.me/theorems/798c353d-c92a-435e-8897-e0dffe4087cd
-- title:
--   The lower occupancy of Algorithm 1
-- statement:
--   $q_k(s,a)=\min_{P'\in\mathcal P_k}q^{P',\pi_k}(s,a)$ on a sample point.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Algorithm 1, line 4, p.16

import Mathlib
import Definitions.Def_IntroDelayAMDP_alg1Policy
import Definitions.Def_IntroDelayAMDP_alg1Conf
import Definitions.Def_IntroDelayAMDP_qLow

namespace IntroDelayAMDP

/-- **The lower occupancy `q_k(s, a) = min_{P′∈P_k} q^{P′,π_k}(s, a)` of Algorithm 1** (line 4, printed
p.16, of Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530)), in the 0-based episode `k` on the sample point `ω`. -/
noncomputable def alg1QLow {St A : Type} [Fintype St] [DecidableEq St] [Fintype A] [Nonempty A] {H K : ℕ}
    (L : LayeredSpace St H) (P : St → A → St → ℝ) (ℓ : ℕ → St → A → ℝ) (p : AlgParams)
    (ω : Tape St A K H) (k : ℕ) : St → A → ℝ :=
  qLow L (alg1Conf L P ℓ p ω k) (alg1Policy L P ℓ p ω k)

end IntroDelayAMDP


