-- Prove2me | Definitions.Def_IntroDelayAMDP_bias1
-- name    : IntroDelayAMDP_bias1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:56:54.195109+00:00
-- url     : https://prove2.me/theorems/f7c15e55-a696-436e-b7a6-1b131cebd155
-- title:
--   Bias-1 of Eq. (28)
-- statement:
--   $\text{Bias-1}=\sum_{k,s,a}q^\star(s)\pi_k(a\mid s)(Q^{\pi_k}_k-\hat Q_k)(s,a)$, for a comparator $\pi^\star$ with $q^\star=q^{\pi^\star}$.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Eq. (28), p.31

import Mathlib
import Definitions.Def_IntroDelayAMDP_alg1Policy
import Definitions.Def_IntroDelayAMDP_alg1QHat
import Definitions.Def_IntroDelayAMDP_alg1BonusQ
import Definitions.Def_IntroDelayAMDP_qFun
import Definitions.Def_IntroDelayAMDP_occS

namespace IntroDelayAMDP

/-- **Bias-1 of Eq. (28)** (printed p.31, of Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530)):
`Bias-1 = ∑_{k,s,a} q⋆(s)π_k(a | s)(Q^{π_k}_k − Q̂_k)(s, a)`, for a comparator policy `π⋆` with
`q⋆ = q^{π⋆}` (state occupancy under the true `P`), summed over the 0-based episodes `k < K`. -/
noncomputable def bias1 {St A : Type} [Fintype St] [DecidableEq St] [Fintype A] [Nonempty A] {H K : ℕ}
    (L : LayeredSpace St H) (P : St → A → St → ℝ) (ℓ : ℕ → St → A → ℝ) (p : AlgParams)
    (ω : Tape St A K H) (πstar : St → A → ℝ) : ℝ :=
  ∑ k ∈ Finset.range K, ∑ s, ∑ a, occS L P πstar s * alg1Policy L P ℓ p ω k s a *
    (qFun L P (ℓ k) (alg1Policy L P ℓ p ω k) s a - alg1QHat L P ℓ p ω k s a)

end IntroDelayAMDP


