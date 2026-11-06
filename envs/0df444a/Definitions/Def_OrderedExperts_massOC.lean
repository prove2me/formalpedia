-- Prove2me | Definitions.Def_OrderedExperts_massOC
-- name    : OrderedExperts_massOC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:32:43.584411+00:00
-- url     : https://prove2.me/theorems/661a0689-93cc-47f2-8573-22cd31ce0c87
-- title:
--   Half-open interval mass $\Pi(a,b]$
-- statement:
--   Let $\pi$ be a vector indexed by the ranks of an ordered chain. The **half-open interval mass** of the ranks $a+1,\dots,b$ is
--   $$
--   \Pi(a,b]=\sum_{r=a+1}^{b}\pi(r).
--   $$
--   It is the normalizer of the jump law of the random increasing path ($P(b\mid a,j)=\pi(b)/\Pi(a,j]$) and appears in the interval flows and edge loads.
-- source:
--   Zuo, Online Learning with Ordered Experts (via Two-point Feedback), STOC 2027 submission (held version, sha256 a6480b1e…fe429), Sec. 3.3, p.8

import Mathlib

namespace OrderedExperts

/-- **Half-open interval mass `Π(a, b]`.** Zuo, *Online Learning with Ordered Experts (via Two-point Feedback)*, STOC 2027 submission (held version), Sec. 3.3, p.8: "Throughout, write
`Π[a, b] = Σ_{r=a}^b π(r)` and `Π(a, b] = Σ_{r=a+1}^b π(r)` for the π-mass of an interval of ranks."

`massOC π a b = Σ_{r=a+1}^b π r`.

**Formalization Note.** Ranks are natural numbers, 1-based with the anchor at rank `0`; `π : ℕ → ℝ`
is read only on the ranks `a+1, …, b`. -/
noncomputable def massOC (π : ℕ → ℝ) (a b : ℕ) : ℝ :=
  ∑ r ∈ Finset.Ioc a b, π r

end OrderedExperts


