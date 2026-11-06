-- Prove2me | Definitions.Def_OrderedExperts_revInterval
-- name    : OrderedExperts_revInterval
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:32:43.196182+00:00
-- url     : https://prove2.me/theorems/605b3442-6377-42bd-ac62-3d85c386f60b
-- title:
--   Revelation probability $q(a,b)$ of an interval edge
-- statement:
--   Let $P(a,b)=\mathbb P(A=a,B=b)$ be the law of the queried pair. When $A\ne B$ the two observed values reveal the increment of the interval edge $E_2=(A\wedge B,A\vee B)$. For ranks $1\le a<b$, its **revelation probability** is
--   $$
--   q(a,b)=\mathbb P(E_2=(a,b))=P(a,b)+P(b,a).
--   $$
-- source:
--   Zuo, Online Learning with Ordered Experts (via Two-point Feedback), STOC 2027 submission (held version, sha256 a6480b1e…fe429), Sec. 3.2, p.7

import Mathlib

namespace OrderedExperts

/-- **Revelation probability of an interval edge.** Zuo, *Online Learning with Ordered Experts (via Two-point Feedback)*, STOC 2027 submission (held version), Sec. 3.2, p.7: "If
`A ≠ B`, the two values together also reveal the increment of the interval edge
`E2 = (A ∧ B, A ∨ B)` [...] `q(a, b) = P(E2 = (a, b))` (`1 ≤ a < b`)."

For a law `P(a, b) = P(A = a, B = b)` of the queried pair and ranks `a < b`,
`revInterval P a b = P(a, b) + P(b, a) = P(E2 = (a, b))`. -/
noncomputable def revInterval (P : ℕ → ℕ → ℝ) (a b : ℕ) : ℝ :=
  P a b + P b a

end OrderedExperts


