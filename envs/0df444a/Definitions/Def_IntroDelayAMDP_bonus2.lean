-- Prove2me | Definitions.Def_IntroDelayAMDP_bonus2
-- name    : IntroDelayAMDP_bonus2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:43:27.383124+00:00
-- url     : https://prove2.me/theorems/01262b4a-ceca-46cd-89b3-0bb2d658dd29
-- title:
--   Second part of the bonus
-- statement:
--   $b^{(2)}(s)=H\sum_a\pi(a\mid s)\mathbf 1[q(s,a)<\theta]$, the part of the bonus (17) covering the other pairs.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), App. A.1, p.30

import Mathlib

namespace IntroDelayAMDP

/-- **Second part of the bonus** `b^{(2)}_k` (App. A.1, p.30). Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), printed p.30: "and
`b^{(2)}_k(s) ≜ H ∑_a π_k(a | s)1[q_k(s, a) < θ]` covers the others".

`bonus2 θ H π q s = H ∑ₐ π(a | s) · 1[q(s, a) < θ]`. -/
noncomputable def bonus2 {St A : Type} [Fintype A] (θ : ℝ) (H : ℕ) (π : St → A → ℝ)
    (q : St → A → ℝ) (s : St) : ℝ :=
  (H : ℝ) * ∑ a, π s a * (if q s a < θ then 1 else 0)

end IntroDelayAMDP


