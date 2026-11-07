-- Prove2me | Definitions.Def_IntroDelayAMDP_coins
-- name    : IntroDelayAMDP_coins
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:45:53.578272+00:00
-- url     : https://prove2.me/theorems/c622b34f-8d42-46e2-8fb9-60ef74c46c9b
-- title:
--   Reading the coins of an episode off the tape
-- statement:
--   Extracts the coins of episode $\kappa$ from a sample point. Every coin is a coordinate of episode $\kappa$. Indices outside the ranges read $0$, and the run never uses them.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Algorithm 1, p.16

import Mathlib
import Definitions.Def_IntroDelayAMDP_Tape
import Definitions.Def_IntroDelayAMDP_EpisodeCoins

namespace IntroDelayAMDP

/-- **Reading the coins of episode `κ` off the tape** (Algorithm 1, printed p.16, of Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530)).
Every coin of `coins ω κ` is a coordinate of episode `κ` (`coordEpisode = κ`); indices outside
`0 ≤ κ, k < K`, `0 ≤ h < H` read `0` and are never used by the run. -/
noncomputable def coins {St A : Type} {K H : ℕ} (ω : Tape St A K H) (κ : ℕ) : EpisodeCoins St A where
  act h := if hk : κ < K ∧ h < H then (ω (Sum.inl (⟨κ, hk.1⟩, ⟨h, hk.2⟩)) : ℝ) else 0
  nxt h := if hk : κ < K ∧ h < H then (ω (Sum.inr (Sum.inl (⟨κ, hk.1⟩, ⟨h, hk.2⟩))) : ℝ) else 0
  acc k s a := if hk : k < K ∧ κ < K then
      (ω (Sum.inr (Sum.inr (Sum.inl (⟨k, hk.1⟩, s, a, ⟨κ, hk.2⟩)))) : ℝ) else 0
  stop k s a := if hk : k < K ∧ κ < K then
      (ω (Sum.inr (Sum.inr (Sum.inr (⟨k, hk.1⟩, s, a, ⟨κ, hk.2⟩)))) : ℝ) else 0

end IntroDelayAMDP


