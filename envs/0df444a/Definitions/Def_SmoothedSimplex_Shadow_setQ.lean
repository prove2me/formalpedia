-- Prove2me | Definitions.Def_SmoothedSimplex_Shadow_setQ
-- name    : SmoothedSimplex_Shadow_setQ
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T12:47:16.589932+00:00
-- url     : https://prove2.me/theorems/231b6cb1-eca0-4a08-b180-3f7e8822b0ab
-- title:
--   Definition 4.0.10 — the set $Q$
-- statement:
--   $Q$ is the set of tuples $(b_1,\dots,b_d)$ of points of $\mathbb R^{d-1}$ satisfying
--
--   1. $\mathrm{dist}(b_1,\mathrm{Aff}(b_2,\dots,b_d))\le 4$,
--   2. $\mathrm{dist}(b_i,b_j)\le 4$ for all $i,j\ge 2$,
--   3. $\mathrm{dist}(b_1^{\perp},b_i)\le 4$ for all $i\ge 2$, where $b_1^{\perp}$ is the orthogonal projection of $b_1$ onto $\mathrm{Aff}(b_2,\dots,b_d)$, and
--   4. $0\in\triangle(b_1,\dots,b_d)$.
--
--   After the change of variables of Corollary 2.5.3, the condition "$(a_1,\dots,a_d)\in P^1_{1,\dots,d}$ and the ray through $q$ meets $\triangle(a_1,\dots,a_d)$" becomes "$(b_1,\dots,b_d)\in Q$" for the in-plane coordinates $b_i$.
--
--   **Formalization Note** The ambient dimension $k$ is a parameter (the paper uses $k=d-1$). Points are indexed by `Fin d`: $b_1$ is index $0$ and $b_2,\dots,b_d$ are the nonzero indices. $\mathrm{dist}(x,\mathrm{Aff}(S))$ is the infimum distance to the affine span; $b_1^\perp$ is the point $p$ of $\mathrm{Aff}(b_2,\dots,b_d)$ with $b_1-p$ orthogonal to its direction.
-- source:
--   Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7, Definition 4.0.10, printed p. 43 (PDF p. 43)

import Mathlib

namespace SmoothedSimplex.Shadow

open scoped RealInnerProductSpace

/-- The set `Q` (Spielman & Teng, arXiv:cs/0111050v7, Definition 4.0.10, printed p. 43,
PDF p. 43): the set of `(b₁, …, b_d)`, `bᵢ ∈ ℝ^{d−1}`, satisfying
1. `dist(b₁, Aff(b₂, …, b_d)) ≤ 4`,
2. `dist(bᵢ, bⱼ) ≤ 4` for all `i, j ≥ 2`,
3. `dist(b₁^⊥, bᵢ) ≤ 4` for all `i ≥ 2`, where `b₁^⊥` is the orthogonal projection of `b₁` onto
   `Aff(b₂, …, b_d)`, and
4. `0 ∈ △(b₁, …, b_d)`.

**Formalization Note.** The points are indexed by `Fin d` (0-based): the paper's `b₁` is index
`0`, and `b₂, …, b_d` are the indices `i ≠ 0`. The ambient space is `ℝ^k` with `k` a parameter;
the paper uses `k = d − 1`. `dist(x, Aff(S))` is `Metric.infDist x (affineSpan ℝ S)`; `b₁^⊥` is
the point `p ∈ Aff(b₂, …, b_d)` with `b₁ − p` orthogonal to the direction of the affine span.
`△(b₁, …, b_d) = ConvHull(b₁, …, b_d)` (§2.1). -/
def setQ {k d : ℕ} [NeZero d] : Set (Fin d → EuclideanSpace ℝ (Fin k)) :=
  {b | Metric.infDist (b 0) (affineSpan ℝ (b '' {i | i ≠ 0}) : Set _) ≤ 4 ∧
       (∀ i j, i ≠ 0 → j ≠ 0 → dist (b i) (b j) ≤ 4) ∧
       (∃ p ∈ affineSpan ℝ (b '' {i | i ≠ 0}),
          (∀ v ∈ (affineSpan ℝ (b '' {i | i ≠ 0})).direction, ⟪b 0 - p, v⟫ = 0) ∧
          ∀ i, i ≠ 0 → dist p (b i) ≤ 4) ∧
       (0 : EuclideanSpace ℝ (Fin k)) ∈ convexHull ℝ (Set.range b)}

end SmoothedSimplex.Shadow


