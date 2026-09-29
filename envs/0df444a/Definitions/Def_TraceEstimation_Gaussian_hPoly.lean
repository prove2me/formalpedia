-- Prove2me | Definitions.Def_TraceEstimation_Gaussian_hPoly
-- name    : TraceEstimation_Gaussian_hPoly
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:27:08.489145+00:00
-- url     : https://prove2.me/theorems/668bd730-156a-4fc2-a50b-34f756e7db38
-- title:
--   Section 5 — the higher-order term $h(t)$ of the moment generating function
-- statement:
--   Let $\lambda_1, \ldots, \lambda_n$ be real numbers (in the paper, the eigenvalues of $A$ listed with multiplicity). For $t \in \mathbb{R}$ define
--
--   $$h(t) = \sum_{s=2}^{n} (-2)^s t^s \sum_{\substack{S \subseteq [n] \\ |S| = s}} \prod_{i \in S} \lambda_i ,$$
--
--   where $[n] = \{1, \ldots, n\}$. With $\tau = \sum_i \lambda_i$, expanding the product gives $\prod_{i=1}^n (1 - 2\lambda_i t) = 1 - 2\tau t + h(t)$, so $h$ collects the terms of degree at least $2$ in $t$. It appears in Eq. (1) of the paper, the moment generating function of $M G_M$.
--
--   **Formalization Note** The paper sums over subsets $S$ of "the set $\Lambda$ of $A$'s eigenvalues"; repeated eigenvalues must be counted with multiplicity for the identity above, so the sum here runs over index sets $S \subseteq [n]$ of size $s$ (`Finset.powersetCard s univ`). For $n \le 1$ the outer sum is empty and $h = 0$.
-- source:
--   Avron and Toledo, Randomized algorithms for estimating the trace of an implicit symmetric positive semi-definite matrix, J. ACM 58(2), Article 8 (2011), pp. 8:7-8:8, Section 5, Eq. (1)

import Mathlib

namespace TraceEstimation.Gaussian

/-- The higher-order part `h(t)` of the moment generating function in Section 5, Eq. (1)
(Avron–Toledo, pp. 8:7–8:8): for a list of eigenvalues `λ_1, …, λ_n` (with multiplicity),
`h(t) = ∑_{s=2}^n (-2)^s t^s ∑_{S ⊆ [n], |S| = s} ∏_{i ∈ S} λ_i`. -/
noncomputable def hPoly {n : ℕ} (lam : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∑ s ∈ Finset.Icc 2 n, (-2 : ℝ) ^ s * t ^ s *
    ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard s, ∏ i ∈ S, lam i

end TraceEstimation.Gaussian


