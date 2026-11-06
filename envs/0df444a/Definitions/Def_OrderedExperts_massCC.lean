-- Prove2me | Definitions.Def_OrderedExperts_massCC
-- name    : OrderedExperts_massCC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:32:40.105247+00:00
-- url     : https://prove2.me/theorems/d37ba3d8-aa46-40bb-8334-d0b0e45e646f
-- title:
--   Closed interval mass $\Pi[a,b]$
-- statement:
--   Let $\pi$ be a vector indexed by the ranks of an ordered chain. The **closed interval mass** of the ranks $a,\dots,b$ is
--   $$
--   \Pi[a,b]=\sum_{r=a}^{b}\pi(r).
--   $$
--   It is the $\pi$-probability of an interval of ranks, used throughout the construction of the endpoint flow estimator: in the flows, the conductances and the edge loads.
--
--   **Formalization Note** Ranks are natural numbers, 1-based with the anchor at rank $0$; $\pi:\mathbb N\to\mathbb R$ is read only on the ranks of the interval.
-- source:
--   Zuo, Online Learning with Ordered Experts (via Two-point Feedback), STOC 2027 submission (held version, sha256 a6480b1e…fe429), Sec. 3.3, p.8

import Mathlib

namespace OrderedExperts

/-- **Closed interval mass `Π[a, b]`.** Zuo, *Online Learning with Ordered Experts (via Two-point Feedback)*, STOC 2027 submission (held version), Sec. 3.3, p.8: "Throughout, write
`Π[a, b] = Σ_{r=a}^b π(r)` and `Π(a, b] = Σ_{r=a+1}^b π(r)` for the π-mass of an interval of ranks."

`massCC π a b = Σ_{r=a}^b π r`.

**Formalization Note.** Ranks are natural numbers, 1-based with the anchor at rank `0`, as in the
paper; a vector on the chain is `π : ℕ → ℝ`, read only on the ranks of the interval. -/
noncomputable def massCC (π : ℕ → ℝ) (a b : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc a b, π r

end OrderedExperts


