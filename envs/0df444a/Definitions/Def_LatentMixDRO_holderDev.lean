-- Prove2me | Definitions.Def_LatentMixDRO_holderDev
-- name    : LatentMixDRO_holderDev
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:24:39.203456+00:00
-- url     : https://prove2.me/theorems/1fdfcae9-2b0e-4569-997a-bdd4e7a2e187
-- title:
--   Wasserstein distance $W_\alpha(\widehat P_n,P)$ in dual form
-- statement:
--   For $\alpha\in(0,1]$ and a metric space $\mathcal Z$, the paper defines
--
--   $$
--   W_\alpha(Q_1,Q_2)=\sup\big\{|\mathbb E_{Q_1}[h]-\mathbb E_{Q_2}[h]|\ \big|\ h:\mathcal Z\to\mathbb R,\ (\alpha,1)\text{-Hölder continuous}\big\}.
--   $$
--
--   This definition is the case $Q_1=\widehat P_n$, $Q_2=P$, on a set $\mathcal Z=S\subset\mathbb R^d\times\mathbb R$ with the Euclidean distance.
--
--   **Formalization Note** The empirical mean is a finite sum, so no empirical measure is built. The real supremum is the true one when $n\ge1$, the sample lies in $S$, $S$ has finite diameter and $P$ is carried by $S$, and every theorem using this definition assumes these. There each test function is $P$-almost everywhere equal to a bounded continuous function, so its integral is genuine.
-- source:
--   Duchi, Hashimoto & Namkoong, Distributionally Robust Losses for Latent Covariate Mixtures, arXiv:2007.13982v2, §4.2, p.11

import Mathlib
import Definitions.Def_LatentMixDRO_dist2

open MeasureTheory

namespace LatentMixDRO

/-- The Wasserstein distance `W_α(P̂_n, P)` in the dual form the paper uses:
`W_α(Q₁, Q₂) = sup {|E_{Q₁}[h] - E_{Q₂}[h]| | h : 𝒵 → ℝ, (α, 1)-Hölder continuous}`,
for `Q₁` the empirical law of the sample `ω` and `Q₂ = P`, on the metric space `𝒵 = S` with the
Euclidean distance `dist2`.

Duchi, Hashimoto & Namkoong, arXiv:2007.13982v2, §4.2, p.11.

**Formalization Note.** The empirical mean is a finite sum, so no empirical measure is built. The
test functions are total, constrained on `S`. The `sSup` is the true supremum when `n ≥ 1`, all
`ω i ∈ S`, `S` has finite `dist2`-diameter and `P` is carried by `S`: every theorem using this
definition assumes these. There each `h` is `P`-a.e. equal to a bounded continuous function, so its
Bochner integral is genuine, and the values are bounded by `diam(S)^α`. -/
noncomputable def holderDev {d n : ℕ} (S : Set (EuclideanSpace ℝ (Fin d) × ℝ)) (α : ℝ)
    (ω : Fin n → EuclideanSpace ℝ (Fin d) × ℝ) (P : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) : ℝ :=
  sSup {v | ∃ h : EuclideanSpace ℝ (Fin d) × ℝ → ℝ,
    (∀ u ∈ S, ∀ u' ∈ S, |h u - h u'| ≤ dist2 u u' ^ α) ∧
    v = |(1 / (n : ℝ)) * (∑ i, h (ω i)) - ∫ u, h u ∂P|}

end LatentMixDRO


