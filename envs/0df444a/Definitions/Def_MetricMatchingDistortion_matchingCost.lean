-- Prove2me | Definitions.Def_MetricMatchingDistortion_matchingCost
-- name    : MetricMatchingDistortion_matchingCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:15:40.766033+00:00
-- url     : https://prove2.me/theorems/2f092ab1-8e0b-46f8-ac3e-b42029002c58
-- title:
--   Cost of a perfect matching $\mathrm{cost}(M,d)$
-- statement:
--   A perfect integral matching is a bijection $\pi$ from agents to items. Its **cost** under $d$ is the total distance
--   $$\mathrm{cost}(\pi,d)=\sum_{a\in A}d(a,\pi(a)).$$
-- source:
--   Charikar, Haqi, Hastings, Huang, Ramakrishnan, Sublinear Metric Distortion for Matching, arXiv:2611.05777 (held version, sha256 fdf3452b105082d6ff680c8a762ec950298417efdebeb216b721705a9802e0da), §2, p.10 (PDF p.12)

import Mathlib

namespace MetricMatchingDistortion

/-- **Cost of a perfect integral matching.** Charikar et al., *Sublinear Metric Distortion for
Matching*, arXiv:2611.05777 (held version, sha256 fdf3452b…), §2, p.10 (PDF p.12): "The cost of an
integral matching M is the sum of assigned distances: cost(M, d) := ∑_{a∈A} d(a, M(a))."

A perfect integral matching is a permutation `π : Equiv.Perm (Fin n)`: agent `a` receives item
`π a`. Agent `a` is the point `Sum.inl a`, item `b` the point `Sum.inr b`. -/
def matchingCost {n : ℕ} (π : Equiv.Perm (Fin n)) (d : Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℝ) : ℝ :=
  ∑ a, d (Sum.inl a) (Sum.inr (π a))

end MetricMatchingDistortion


