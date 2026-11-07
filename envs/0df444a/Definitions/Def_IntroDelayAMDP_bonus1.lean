-- Prove2me | Definitions.Def_IntroDelayAMDP_bonus1
-- name    : IntroDelayAMDP_bonus1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:43:13.803685+00:00
-- url     : https://prove2.me/theorems/9ac57987-8b4c-4ba9-8c9a-26640c2e8994
-- title:
--   First part of the bonus
-- statement:
--   $b^{(1)}(s)=c_1\eta H^3\sum_a\pi(a\mid s)\mathbf 1[q(s,a)\ge\theta]/q(s,a)$, the part of the bonus (17) covering the estimated pairs.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), App. A.1, p.30

import Mathlib

namespace IntroDelayAMDP

/-- **First part of the bonus** `b^{(1)}_k` (App. A.1, p.30). Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), printed p.30: "We also split
the bonus in Eq. (17) as `b_k = b^{(1)}_k + b^{(2)}_k`, where `b^{(1)}_k(s) ≜ c₁ηH³ ∑_a
π_k(a | s)1[q_k(s, a) ≥ θ]/q_k(s, a)` covers the estimated pairs".

`bonus1 c₁ η θ H π q s = c₁ηH³ ∑ₐ π(a | s) · 1[q(s, a) ≥ θ] / q(s, a)`. -/
noncomputable def bonus1 {St A : Type} [Fintype A] (c1 η θ : ℝ) (H : ℕ) (π : St → A → ℝ)
    (q : St → A → ℝ) (s : St) : ℝ :=
  c1 * η * (H : ℝ) ^ 3 * ∑ a, π s a * (if θ ≤ q s a then 1 / q s a else 0)

end IntroDelayAMDP


