-- Prove2me | Definitions.Def_IntroDelayAMDP_alg1Bonus
-- name    : IntroDelayAMDP_alg1Bonus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:54:59.384216+00:00
-- url     : https://prove2.me/theorems/ed6d7649-7075-48bc-a04a-3593961abc19
-- title:
--   The bonus of Algorithm 1
-- statement:
--   $b_k$ of (17) on a sample point.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Eq. (17), p.16

import Mathlib
import Definitions.Def_IntroDelayAMDP_alg1QLow
import Definitions.Def_IntroDelayAMDP_bonus

namespace IntroDelayAMDP

/-- **The bonus `b_k` of Algorithm 1** (Eq. (17), line 4, printed p.16, of Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530)) in the 0-based
episode `k` on the sample point `ω`. -/
noncomputable def alg1Bonus {St A : Type} [Fintype St] [DecidableEq St] [Fintype A] [Nonempty A] {H K : ℕ}
    (L : LayeredSpace St H) (P : St → A → St → ℝ) (ℓ : ℕ → St → A → ℝ) (p : AlgParams)
    (ω : Tape St A K H) (k : ℕ) : St → ℝ :=
  bonus p.c1 p.eta p.theta H (alg1Policy L P ℓ p ω k) (alg1QLow L P ℓ p ω k)

end IntroDelayAMDP


