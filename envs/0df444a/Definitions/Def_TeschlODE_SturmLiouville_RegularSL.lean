-- Prove2me | Definitions.Def_TeschlODE_SturmLiouville_RegularSL
-- name    : TeschlODE_SturmLiouville_RegularSL
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T11:20:36.344932+00:00
-- url     : https://prove2.me/theorems/1b918274-7be9-42f4-9d09-730e5d244e28
-- title:
--   Regular Sturm–Liouville coefficients (5.45)
-- statement:
--   Let $a < b$ and let $p, q, r : [a,b] \to \mathbb{R}$. The Sturm–Liouville equation
--   $$-(p(x) y')' + (q(x) - z\, r(x))\, y = 0 \qquad (5.43)$$
--   is **regular** on $[a,b]$ if
--   $$r, q \in C^0([a,b], \mathbb{R}), \qquad p \in C^1([a,b], \mathbb{R}), \qquad p(x) > 0,\ r(x) > 0 \ \text{ for } x \in [a,b]. \qquad (5.45)$$
--   The book imposes (5.45) "for the rest of this chapter"; every theorem of this mission takes it as a hypothesis.
--
--   **Formalization Note.** $p, q, r$ are total functions $\mathbb{R} \to \mathbb{R}$ and only their values on `Set.Icc a b` enter. $C^1$ on the closed interval is `ContDiffOn ℝ 1 p (Set.Icc a b)` (derivatives within the interval, one-sided at the endpoints). The condition $a < b$ is part of the definition.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 153, §5.3, Eq. (5.45)

import Mathlib

namespace TeschlODE.SturmLiouville

/-- Teschl §5.3, p. 153, (5.45), the standing assumption for the rest of Chapter 5: on the
compact interval `[a, b]` (with `a < b`) the coefficients satisfy `r, q ∈ C⁰([a, b], ℝ)`,
`p ∈ C¹([a, b], ℝ)` and `p(x), r(x) > 0` for `x ∈ [a, b]`; the Sturm–Liouville equation (5.43)
is then called *regular*. Only the values of `p, q, r` on `[a, b]` matter. -/
def RegularSL (p q r : ℝ → ℝ) (a b : ℝ) : Prop :=
  a < b ∧ ContinuousOn r (Set.Icc a b) ∧ ContinuousOn q (Set.Icc a b) ∧
    ContDiffOn ℝ 1 p (Set.Icc a b) ∧ ∀ x ∈ Set.Icc a b, 0 < p x ∧ 0 < r x

end TeschlODE.SturmLiouville


