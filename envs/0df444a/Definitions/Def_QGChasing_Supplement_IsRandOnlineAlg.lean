-- Prove2me | Definitions.Def_QGChasing_Supplement_IsRandOnlineAlg
-- name    : QGChasing_Supplement_IsRandOnlineAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:26:49.600596+00:00
-- url     : https://prove2.me/theorems/ee0dea1c-0173-45ea-84c4-57422bc4edc8
-- title:
--   Randomized online algorithm on $\mathbb R^d$ (§5.2)
-- statement:
--   A **randomized online algorithm** on $\mathbb R^d$ started at $x_0$ has an internal random seed $\omega$ from a measurable space $\Omega$. Given the seed and the request sequence $f=(f_1,f_2,\dots)$ it plays decisions $x_0,x_1,\dots$, where
--
--   1. $x_0$ is the given start point;
--   2. $x_t$ depends only on the seed and $f_1,\dots,f_t$ (nonanticipativity);
--   3. each $x_t$ is a measurable function of the seed, for every fixed request sequence.
--
--   The seed's law is a probability measure supplied with the algorithm. The seed is independent of the requests, which are fixed in advance (an oblivious adversary).
--
--   **Formalization Note** The algorithm is a map $\Omega\to(\text{requests})\to\mathbb N\to\mathbb R^d$ with $\Omega$ in `Type`. There is no feasibility clause because the lower bound uses $X=\mathbb R^d$. The algorithm may depend on the dimension and on the horizon.
-- source:
--   He–Yang–Jiang–Zhang, Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth, STOC 2027 submission (manuscript sha256 ba253cd3…02239), §5.2 and Lemma 5.3, p.12; Appendix A.7, p.20

import Mathlib

namespace QGChasing.Supplement

/-- A randomized online algorithm on `ℝᵈ` started at `x₀` (He–Yang–Jiang–Zhang, *Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth*, STOC 2027 submission manuscript (sha256 ba253cd3…02239), §5.2 and Lemma 5.3, p.12;
Appendix A.7, p.20). The internal randomness is a seed `ω` of a measurable space `Ω`; given the seed
and the request sequence `f = (f₁, f₂, …)`, the algorithm's decisions are `x ω f 0, x ω f 1, …`. It is
an online algorithm when

1. it starts at `x₀`: `x ω f 0 = x₀`;
2. it is nonanticipative: `x_t` depends only on `f₁, …, f_t` (and the seed);
3. each decision is a measurable function of the seed, for every fixed request sequence and round.

**Formalization Note** The seed's law is a probability measure on `Ω` supplied separately. The seed
does not depend on the requests, and the requests are a fixed argument (an oblivious adversary).
The feasible set is all of `ℝᵈ`, as in the lower bound of the source (`X = ℝᵈ`, p.11), so no
feasibility clause is needed. The algorithm may depend on the dimension and on the horizon, which
the theorem fixes before quantifying over algorithms. -/
def IsRandOnlineAlg {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (x₀ : EuclideanSpace ℝ (Fin d))
    (x : Ω → (ℕ → EuclideanSpace ℝ (Fin d) → ℝ) → ℕ → EuclideanSpace ℝ (Fin d)) : Prop :=
  (∀ ω f, x ω f 0 = x₀) ∧
  (∀ ω f f' t, (∀ s, 1 ≤ s → s ≤ t → f s = f' s) → x ω f t = x ω f' t) ∧
  (∀ f t, Measurable fun ω => x ω f t)

end QGChasing.Supplement


