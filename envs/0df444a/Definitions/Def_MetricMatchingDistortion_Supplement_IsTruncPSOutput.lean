-- Prove2me | Definitions.Def_MetricMatchingDistortion_Supplement_IsTruncPSOutput
-- name    : MetricMatchingDistortion_Supplement_IsTruncPSOutput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:02:36.539008+00:00
-- url     : https://prove2.me/theorems/35380e48-4590-43fb-be9e-150ef108009e
-- title:
--   Admissible outputs of TruncatedPS with doubling: bistochastic $Y\le 2X(1-\frac1{2n})$
-- statement:
--   Let $X(t)$ be the matrix maintained by the Probabilistic Serial rule at time $t$, and $T=1-\frac1{2n}$. A matrix $Y$ indexed by agents and items is an **admissible output of TruncatedPS with doubling** (Algorithm 8) if $Y$ is bistochastic (nonnegative, every row and column sums to $1$) and
--   $$Y_{a,b}\le 2X_{a,b}(T)\quad\text{for every agent }a\text{ and item }b.$$
--
--   Algorithm 8 returns any such $Y$, read as a lottery over perfect integral matchings with marginals $Y$; its expected cost is then $\mathrm{cost}(Y,d)=\sum_{a,b}Y_{a,b}d(a,b)$. Such $Y$ exist by Lemma 6.14.
--
--   **Formalization Note** $X$ is the published `psAlloc`; $\frac1{2n}$ is real division with $n\ge1$.
-- source:
--   Charikar, Haqi, Hastings, Huang, Ramakrishnan, Sublinear Metric Distortion for Matching, arXiv:2611.05777 (held version, sha256 fdf3452b105082d6ff680c8a762ec950298417efdebeb216b721705a9802e0da), Algorithm 8, p.63 (PDF p.65)

import Mathlib
import Definitions.Def_MetricMatchingDistortion_IsPartialFractionalMatching
import Definitions.Def_MetricMatchingDistortion_psAlloc

namespace MetricMatchingDistortion.Supplement

open MetricMatchingDistortion

/-- **Admissible outputs of TruncatedPS with doubling (Algorithm 8).** Charikar et al., *Sublinear
Metric Distortion for Matching*, arXiv:2611.05777 (held version, sha256 fdf3452b…), Algorithm 8,
p.63 (PDF p.65): "Let X(T) be the matrix maintained by PS at time T = 1 − 1/(2n). Let Y be any
bistochastic matrix with Y ≤ 2X(T) (guaranteed by Lemma 6.14). Return Y." and "We write TruncPS for
TruncatedPS with doubling and, as with PS, interpret its output Y as a distribution over perfect
integral matchings with marginals Y."

`IsTruncPSOutput rk Y` says that `Y` is a perfect fractional (bistochastic) matrix with
`Y a b ≤ 2 · X_{a,b}(1 − 1/(2n))` for every agent `a` and item `b`, where `X` is the base mission's
PS trajectory `psAlloc`.

**Formalization Note.** The algorithm may return any such `Y`; theorems about TruncPS quantify over
every admissible `Y`. Its expected cost is `fracCost Y d`, the cost of the marginals, which is the
expected cost of any lottery over perfect integral matchings with marginals `Y`. `1/(2n)` is real
division, with `n ≥ 1` from `[NeZero n]`. -/
def IsTruncPSOutput {n : ℕ} [NeZero n] (rk : Ranking n) (Y : Fin n → Fin n → ℝ) : Prop :=
  IsPerfectFractionalMatching Y ∧
    ∀ a b, Y a b ≤ 2 * psAlloc rk (1 - 1 / (2 * (n : ℝ))) a b

end MetricMatchingDistortion.Supplement


