-- Prove2me | Definitions.Def_IntroDelayAMDP_regTerm
-- name    : IntroDelayAMDP_regTerm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:57:16.408201+00:00
-- url     : https://prove2.me/theorems/a91807c7-a038-4ba8-a7d7-b2c56e2bd87e
-- title:
--   Reg-Term of Eq. (28)
-- statement:
--   $\text{Reg-Term}=\sum_{k,s,a}q^\star(s)(\pi_k-\pi^\star)(a\mid s)(\hat Q_k-B_k)(s,a)$.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Eq. (28), p.31

import Mathlib
import Definitions.Def_IntroDelayAMDP_alg1Policy
import Definitions.Def_IntroDelayAMDP_alg1QHat
import Definitions.Def_IntroDelayAMDP_alg1BonusQ
import Definitions.Def_IntroDelayAMDP_qFun
import Definitions.Def_IntroDelayAMDP_occS

namespace IntroDelayAMDP

/-- **Reg-Term of Eq. (28)** (printed p.31, of Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530)):
`Reg-Term = ∑_{k,s,a} q⋆(s)(π_k − π⋆)(a | s)(Q̂_k − B_k)(s, a)`. -/
noncomputable def regTerm {St A : Type} [Fintype St] [DecidableEq St] [Fintype A] [Nonempty A] {H K : ℕ}
    (L : LayeredSpace St H) (P : St → A → St → ℝ) (ℓ : ℕ → St → A → ℝ) (p : AlgParams)
    (ω : Tape St A K H) (πstar : St → A → ℝ) : ℝ :=
  ∑ k ∈ Finset.range K, ∑ s, ∑ a, occS L P πstar s * (alg1Policy L P ℓ p ω k s a - πstar s a) *
    (alg1QHat L P ℓ p ω k s a - alg1BonusQ L P ℓ p ω k s a)

end IntroDelayAMDP


