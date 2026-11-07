-- Prove2me | Definitions.Def_SmoothedMIS_smoothLaw
-- name    : SmoothedMIS_smoothLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:47:42.906561+00:00
-- url     : https://prove2.me/theorems/9cdf4ff5-480d-4b1b-b27b-4b7e1b4c4379
-- title:
--   The smoothing: $\mathcal G=G\cup R$, $G_s=G\triangle G(n,p)$, $p=\beta\ln n/n$
-- statement:
--   Let $G$ be a base graph on the vertex set $\{0,\dots,n-1\}$ and $\beta>0$. Give every vertex pair an independent coin that is true with probability
--   $$
--   p=\frac{\beta\ln n}{n}.
--   $$
--   The **addition-only smoothing** $\mathcal G=G\cup R$ adds every pair whose coin is true; equivalently, every non-edge of $G$ enters the set $R$ of random edges independently with probability $p$ (§2). The **symmetric-difference smoothing** $G_s=G\triangle G(n,p)$ flips every pair whose coin is true: a non-edge becomes an edge and an edge becomes a non-edge (§1.5).
--
--   The law of the coins is the smoothing law of the mission; Theorem 4.1 is about $\mathcal G$ and the goal, Theorem 4.14, about $G_s$.
--
--   **Formalization Note** Logarithms are natural. The probability is $\min(1,\beta\ln n/n)$, which equals $\beta\ln n/n$ once $\beta\ln n\le n$, i.e. for all large $n$. Coins on edges of $G$ do not change $\mathcal G$, so $\mathcal G$ has exactly the law of $G\cup R$.
-- source:
--   Dey, Dufoulon, Moses Jr., Pandurangan, Smoothed Analysis for Distributed MIS (manuscript, STOC 2027 submission, sha256 dc2131db058466142db72a65b8482787f2b03f36c54eb18702fb92825cdfb42d), §1.5 "Smoothing Model", p.4 (PDF p.6); §2, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_SmoothedMIS_coinLaw

open MeasureTheory

namespace SmoothedMIS

/-- The smoothing probability `p = β ln n / n`, clamped to at most `1`. -/
noncomputable def smoothProb (n : ℕ) (β : ℝ) : ℝ := min 1 (β * Real.log n / n)

/-- The **addition-only smoothing** `𝒢 = G ∪ R` (§2, p.9): the base graph together with every
pair whose coin is `true`. Under `smoothLaw n β`, the pairs that are not edges of `G` enter
independently with probability `p`, so `addSmooth G ω` has the law of `G ∪ G(n, p)`; coins on
edges of `G` and on diagonal pairs have no effect. -/
def addSmooth {n : ℕ} (G : SimpleGraph (Fin n)) (ω : Sym2 (Fin n) → Bool) :
    SimpleGraph (Fin n) :=
  G ⊔ SimpleGraph.fromEdgeSet {e | ω e = true}

/-- The **symmetric-difference smoothing** `Gs = G △ G(n, p)` (§1.5, p.4): every pair whose coin
is `true` is flipped (a non-edge becomes an edge, an edge becomes a non-edge). -/
def symmSmooth {n : ℕ} (G : SimpleGraph (Fin n)) (ω : Sym2 (Fin n) → Bool) :
    SimpleGraph (Fin n) :=
  symmDiff G (SimpleGraph.fromEdgeSet {e | ω e = true})

/-- **The smoothing law** (Dey, Dufoulon, Moses Jr., Pandurangan, *Smoothed Analysis for
Distributed MIS* (manuscript, sha256 dc2131db…), §1.5, p.4, and §2, p.9): independent coins on
the vertex pairs of `Fin n`, each `true` with probability `p = β ln n/n`.

**Formalization Note** Vertices are `Fin n`; `ln` is `Real.log`. The probability is clamped to
`min 1 (β ln n/n)`; the clamp is the identity as soon as `β ln n ≤ n`, i.e. for all large `n`. -/
noncomputable def smoothLaw (n : ℕ) (β : ℝ) : Measure (Sym2 (Fin n) → Bool) :=
  coinLaw (Sym2 (Fin n)) (smoothProb n β)

end SmoothedMIS


