-- Prove2me | Definitions.Def_OrderedExperts_revAnchor
-- name    : OrderedExperts_revAnchor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:32:42.803938+00:00
-- url     : https://prove2.me/theorems/48daa0b0-25c4-4f74-9c80-e183e489602f
-- title:
--   Revelation probability $q(0,a)$ of an anchor edge
-- statement:
--   Let $P(a,b)=\mathbb P(A=a,B=b)$ be the law of the queried pair of ranks on $\{1,\dots,m\}^2$. Since $g(x_0)=0$, the value $g(x_A)$ alone reveals the increment of the anchor edge $E_1=(0,A)$. The **revelation probability** of the anchor edge $(0,a)$ is
--   $$
--   q(0,a)=\mathbb P(E_1=(0,a))=\sum_{b=1}^m P(a,b)=\mathbb P(A=a).
--   $$
-- source:
--   Zuo, Online Learning with Ordered Experts (via Two-point Feedback), STOC 2027 submission (held version, sha256 a6480b1e…fe429), Sec. 3.2, p.7

import Mathlib

namespace OrderedExperts

/-- **Revelation probability of an anchor edge.** Zuo, *Online Learning with Ordered Experts (via Two-point Feedback)*, STOC 2027 submission (held version), Sec. 3.2, p.7: "Since
`g(x0) = 0`, the value `g(xA)` alone reveals the increment of the anchor edge `E1 = (0, A)`. [...] The
revelation probability `q(e)` of an edge is the probability that its increment is revealed:
`q(0, a) = P(E1 = (0, a))`".

For a law `P(a, b) = P(A = a, B = b)` of the queried pair on the active ranks `{1, …, m}²`,
`revAnchor m P a = Σ_{b=1}^m P(a, b) = P(A = a) = q(0, a)`. -/
noncomputable def revAnchor (m : ℕ) (P : ℕ → ℕ → ℝ) (a : ℕ) : ℝ :=
  ∑ b ∈ Finset.Icc 1 m, P a b

end OrderedExperts


