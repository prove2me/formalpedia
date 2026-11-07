-- Prove2me | Definitions.Def_IntroDelayAMDP_bonusTerm
-- name    : IntroDelayAMDP_bonusTerm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:57:00.576195+00:00
-- url     : https://prove2.me/theorems/4ffb3cb6-4867-493e-8427-bccf6d82ef02
-- title:
--   Bonus of Eq. (28)
-- statement:
--   $\text{Bonus}=\sum_{k,s,a}q^\star(s)(\pi_k-\pi^\star)(a\mid s)B_k(s,a)$.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Eq. (28), p.31

import Mathlib
import Definitions.Def_IntroDelayAMDP_alg1Policy
import Definitions.Def_IntroDelayAMDP_alg1QHat
import Definitions.Def_IntroDelayAMDP_alg1BonusQ
import Definitions.Def_IntroDelayAMDP_qFun
import Definitions.Def_IntroDelayAMDP_occS

namespace IntroDelayAMDP

/-- **Bonus of Eq. (28)** (printed p.31, of Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530)):
`Bonus = ∑_{k,s,a} q⋆(s)(π_k − π⋆)(a | s)B_k(s, a)`. -/
noncomputable def bonusTerm {St A : Type} [Fintype St] [DecidableEq St] [Fintype A] [Nonempty A] {H K : ℕ}
    (L : LayeredSpace St H) (P : St → A → St → ℝ) (ℓ : ℕ → St → A → ℝ) (p : AlgParams)
    (ω : Tape St A K H) (πstar : St → A → ℝ) : ℝ :=
  ∑ k ∈ Finset.range K, ∑ s, ∑ a, occS L P πstar s * (alg1Policy L P ℓ p ω k s a - πstar s a) *
    alg1BonusQ L P ℓ p ω k s a

end IntroDelayAMDP


