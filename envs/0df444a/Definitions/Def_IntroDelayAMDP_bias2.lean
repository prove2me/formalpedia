-- Prove2me | Definitions.Def_IntroDelayAMDP_bias2
-- name    : IntroDelayAMDP_bias2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:57:03.190856+00:00
-- url     : https://prove2.me/theorems/c38d175a-4bae-4771-b016-fada9ec854eb
-- title:
--   Bias-2 of Eq. (28)
-- statement:
--   $\text{Bias-2}=\sum_{k,s,a}q^\star(s)\pi^\star(a\mid s)(\hat Q_k-Q^{\pi_k}_k)(s,a)$.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Eq. (28), p.31

import Mathlib
import Definitions.Def_IntroDelayAMDP_alg1Policy
import Definitions.Def_IntroDelayAMDP_alg1QHat
import Definitions.Def_IntroDelayAMDP_alg1BonusQ
import Definitions.Def_IntroDelayAMDP_qFun
import Definitions.Def_IntroDelayAMDP_occS

namespace IntroDelayAMDP

/-- **Bias-2 of Eq. (28)** (printed p.31, of Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530)):
`Bias-2 = ∑_{k,s,a} q⋆(s)π⋆(a | s)(Q̂_k − Q^{π_k}_k)(s, a)`. -/
noncomputable def bias2 {St A : Type} [Fintype St] [DecidableEq St] [Fintype A] [Nonempty A] {H K : ℕ}
    (L : LayeredSpace St H) (P : St → A → St → ℝ) (ℓ : ℕ → St → A → ℝ) (p : AlgParams)
    (ω : Tape St A K H) (πstar : St → A → ℝ) : ℝ :=
  ∑ k ∈ Finset.range K, ∑ s, ∑ a, occS L P πstar s * πstar s a *
    (alg1QHat L P ℓ p ω k s a - qFun L P (ℓ k) (alg1Policy L P ℓ p ω k) s a)

end IntroDelayAMDP


