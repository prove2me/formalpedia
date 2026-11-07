-- Prove2me | Definitions.Def_KMeansTaper_lp2
-- name    : KMeansTaper_lp2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:05:18.482202+00:00
-- url     : https://prove2.me/theorems/2bb9e8fe-2706-43c1-9ea4-0152e462be9c
-- title:
--   The squared LP value $\mathrm{LP}_2$ and correct additive outputs
-- statement:
--   For an instance $I$, $\mathrm{LP}_2$ is the optimum of the natural LP relaxation with squared distances:
--
--   $$\mathrm{LP}_2=\min\Bigl\{\sum_{j\in J}\sum_{i\in F}d(j,i)^2x_{ji}:\ 0\le x_{ji}\le y_i\le1,\ \sum_{i\in F}x_{ji}=1\ (j\in J),\ \sum_{i\in F}y_i\le k\Bigr\}.$$
--
--   An output is **$(\rho,c)$-additively correct** if it is the indicator list of a set $S$ with $\emptyset\ne S\subseteq F$, $|S|\le k+c$ and $\mathrm{cost}_2(S)\le\rho\cdot\mathrm{LP}_2$.
--
--   The LP is the benchmark of the two rounding stages (Theorem 7.1); it is at most $\mathrm{OPT}_k$.
--
--   **Formalization Note** The paper refers to the LP of its reference [35, (2.1)] without printing it; the mission pins it as the standard k-median relaxation above (the bound $y_i\le1$ does not change the optimum). The value is an infimum of a nonempty set of nonnegative reals.
-- source:
--   Zhu, A tight approximation for metric k-means via squared tapered rounding, STOC 2027 submission (manuscript sha256 8b6610229e43dc2441325b120437136afe762dbd6e873f73919fcb6b043fc5a3), Section 2 ("Problem"), p.3 (PDF p.6); Theorem 7.1, p.17 (PDF p.20)

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_KMeansTaper_cost2

namespace KMeansTaper

open OAI.MetricKMedian (Instance)

/-- **The squared LP value `LP₂`**, Section 2, p.3 (PDF p.6): the LP of [35, (2.1)] with
objective `∑_{j,i} d(j, i)² x_{ij}`, here the standard k-median relaxation
`min ∑_{j ∈ J} ∑_{i ∈ F} d(j, i)² x_{ji}` subject to `0 ≤ x_{ji} ≤ y_i ≤ 1`,
`∑_{i ∈ F} x_{ji} = 1` for every client `j`, and `∑_{i ∈ F} y_i ≤ k`.

Zhu, *A tight approximation for metric k-means via squared tapered rounding*, STOC 2027
submission (manuscript sha256 8b661022…fc5a3).

**Formalization Note.** The paper does not print the LP of [35, (2.1)]; the mission pins it as
the standard relaxation above (the bound `y_i ≤ 1` does not change the optimum). The value is an
`sInf` of a nonempty set bounded below by `0` (every integral solution is feasible). -/
noncomputable def lp2 (I : Instance) : ℝ :=
  sInf {v : ℝ | ∃ (x : Fin I.n → Fin I.n → ℝ) (y : Fin I.n → ℝ),
    (∀ j i, 0 ≤ x j i ∧ x j i ≤ y i) ∧ (∀ i, y i ≤ 1) ∧
    (∀ j ∈ I.clients, ∑ i ∈ I.facilities, x j i = 1) ∧ ∑ i ∈ I.facilities, y i ≤ I.k ∧
    v = ∑ j ∈ I.clients, ∑ i ∈ I.facilities, (I.distance j i : ℝ) ^ 2 * x j i}

/-- **A correct additive output**, Theorem 7.1, p.17 (PDF p.20): the indicator bit-list of a
nonempty `S ⊆ F` with `|S| ≤ k + c` and `cost₂(S) ≤ ρ · LP₂`. -/
def CorrectAdditive (ρ : ℝ) (c : ℕ) (I : Instance) (output : List Bool) : Prop :=
  ∃ S : Finset (Fin I.n), S ⊆ I.facilities ∧ S.Nonempty ∧ S.card ≤ I.k + c ∧
    output = mask I S ∧ cost2 I S ≤ ρ * lp2 I

end KMeansTaper


