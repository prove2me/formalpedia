-- Prove2me | Definitions.Def_KMeansTaper_CorrectRatio
-- name    : KMeansTaper_CorrectRatio
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:05:17.110583+00:00
-- url     : https://prove2.me/theorems/85d5db9b-dac0-467a-8b86-17dcdafd9362
-- title:
--   A correct $\rho$-approximate output for metric k-means
-- statement:
--   Let $I$ be an instance and $\rho$ a real number. An output list of bits is **$\rho$-correct** for $I$ if it is the indicator list of a set $S$ with
--
--   1. $\emptyset\ne S\subseteq F$ and $|S|\le k$, and
--   2. $\displaystyle\sum_{j\in J} d(j,S)^2\le \rho\cdot \mathrm{OPT}_k$.
--
--   This is what "returns $S\subseteq F$ with $|S|\le k$ and $\sum_j d(j,S)^2\le(1+\kappa/e+\varepsilon)\mathrm{OPT}_k$" means in Theorems 3.1 and 3.3.
--
--   **Formalization Note** It is the published k-median predicate `OAI.MetricKMedian.Correct` with squared costs and a general ratio. Nonemptiness excludes the empty set, whose paper cost is infinite.
-- source:
--   Zhu, A tight approximation for metric k-means via squared tapered rounding, STOC 2027 submission (manuscript sha256 8b6610229e43dc2441325b120437136afe762dbd6e873f73919fcb6b043fc5a3), Theorems 3.1 and 3.3, p.4 (PDF p.7)

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_KMeansTaper_cost2

namespace KMeansTaper

open OAI.MetricKMedian (Instance)

/-- **A correct `ρ`-approximate output** for metric k-means with candidate centers, Theorems 3.1
and 3.3, p.4 (PDF p.7): the output is the indicator bit-list of a set `S ⊆ F` with `S ≠ ∅`,
`|S| ≤ k` and `∑_{j ∈ J} d(j, S)² ≤ ρ · OPT_k`.

Zhu, *A tight approximation for metric k-means via squared tapered rounding*, STOC 2027
submission (manuscript sha256 8b661022…fc5a3).

**Formalization Note.** `S ≠ ∅` excludes the junk value `cost2 I ∅ = 0`; the paper's `S = ∅`
has infinite cost, so this changes no instance. The shape is that of the published
`OAI.MetricKMedian.Correct` (k-median, ratio `1 + 2/e + ε`) with squared costs and a general
ratio `ρ`. -/
def CorrectRatio (ρ : ℝ) (I : Instance) (output : List Bool) : Prop :=
  ∃ S : Finset (Fin I.n), S ⊆ I.facilities ∧ S.Nonempty ∧ S.card ≤ I.k ∧
    output = mask I S ∧ cost2 I S ≤ ρ * optimum2 I

end KMeansTaper


