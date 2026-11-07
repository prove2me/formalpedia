-- Prove2me | Definitions.Def_IntroDelayAMDP_bonus
-- name    : IntroDelayAMDP_bonus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:42:57.227956+00:00
-- url     : https://prove2.me/theorems/76f459e8-a954-495d-bc7f-1a712400c564
-- title:
--   Thresholding bonus, Eq. (17)
-- statement:
--   For parameters $c_1,\eta,\theta$, a policy $\pi$ and lower occupancies $q$,
--   $$b(s)=\sum_a\pi(a\mid s)\Bigl(\frac{c_1\eta H^3}{q(s,a)}\mathbf 1[q(s,a)\ge\theta]+H\,\mathbf 1[q(s,a)<\theta]\Bigr).$$
--
--   **Formalization Note** The two indicators are complementary, so they are one `if`. The division occurs only when $q(s,a)\ge\theta$.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Eq. (17), Algorithm 1 line 4, p.16

import Mathlib

namespace IntroDelayAMDP

/-- **Thresholding bonus** `b_κ(s)` (Eq. (17), Algorithm 1 line 4, p.16). Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), printed p.16:
"`b_κ(s) ≜ ∑_{a∈A} π_κ(a | s) (c₁ηH³/q_κ(s, a) · 1[q_κ(s, a) ≥ θ] + H · 1[q_κ(s, a) < θ])`. (17)"

For the parameters `c₁, η, θ`, the horizon `H`, a policy `π` and the lower occupancies `q`,
`bonus c₁ η θ H π q s = ∑ₐ π(a | s) · (c₁ηH³/q(s, a) if q(s, a) ≥ θ, else H)`.

**Formalization Note.** The two indicators of (17) are complementary, so they are written as one
`if`; the division by `q(s, a)` only occurs when `q(s, a) ≥ θ > 0`. -/
noncomputable def bonus {St A : Type} [Fintype A] (c1 η θ : ℝ) (H : ℕ) (π : St → A → ℝ)
    (q : St → A → ℝ) (s : St) : ℝ :=
  ∑ a, π s a * (if θ ≤ q s a then c1 * η * (H : ℝ) ^ 3 / q s a else (H : ℝ))

end IntroDelayAMDP


