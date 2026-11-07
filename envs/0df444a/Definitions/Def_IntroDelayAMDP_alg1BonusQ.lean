-- Prove2me | Definitions.Def_IntroDelayAMDP_alg1BonusQ
-- name    : IntroDelayAMDP_alg1BonusQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:56:00.426203+00:00
-- url     : https://prove2.me/theorems/da5a236b-a54b-4fb2-b64f-bd63bbcd837f
-- title:
--   The bonus Q-function of Algorithm 1
-- statement:
--   $B_k$ of (18) on a sample point.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Eq. (18), p.16

import Mathlib
import Definitions.Def_IntroDelayAMDP_alg1Bonus
import Definitions.Def_IntroDelayAMDP_bonusQ

namespace IntroDelayAMDP

/-- **The bonus Q-function `B_k` of Algorithm 1** (Eq. (18), line 5, printed p.16, of Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530)) in the
0-based episode `k` on the sample point `ω`. -/
noncomputable def alg1BonusQ {St A : Type} [Fintype St] [DecidableEq St] [Fintype A] [Nonempty A] {H K : ℕ}
    (L : LayeredSpace St H) (P : St → A → St → ℝ) (ℓ : ℕ → St → A → ℝ) (p : AlgParams)
    (ω : Tape St A K H) (k : ℕ) : St → A → ℝ :=
  bonusQ L (alg1Conf L P ℓ p ω k) (alg1Policy L P ℓ p ω k) (alg1Bonus L P ℓ p ω k)

end IntroDelayAMDP


