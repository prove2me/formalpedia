-- Prove2me | Definitions.Def_UnionVolEst_estGood
-- name    : UnionVolEst_estGood
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:04:34.562207+00:00
-- url     : https://prove2.me/theorems/f37253ee-da8b-40f2-a785-9310bf4d7f6a
-- title:
--   $\mathrm{Est}_{\mathrm{good}}=\sum_j Y_j$
-- statement:
--   For a multiset $X$, $\mathrm{Est}_{\mathrm{good}} = \sum_{j} Y_j$ where $Y_j$ is the number of points of $X$ in the good part $\hat K_j\setminus \mathrm{Bad}_j$ of the $j$-th unique section.
-- source:
--   Banerjee, Bal, Basu, Chakraborty, Chanda, Sarkar, Estimating the Volume of a Union of Convex Bodies, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), §5.1, p.18 (PDF p.20); §5.2.4, p.24 (PDF p.26)

import Mathlib
import Definitions.Def_UnionVolEst_countIn
import Definitions.Def_UnionVolEst_uniqueSection
import Definitions.Def_UnionVolEst_badRegion

namespace UnionVolEst

/-- `Est_good = Σ_j Y_j`, the number of stored samples lying in the good parts `K̂_j \ Bad_j`
(Banerjee–Bal–Basu–Chakraborty–Chanda–Sarkar, *Estimating the Volume of a Union of Convex Bodies*, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), §5.1, printed p.18, and §5.2.4, printed p.24, PDF pp.20, 26), for a multiset `X`. -/
noncomputable def estGood {n M : ℕ} (K : Fin M → Set (EuclideanSpace ℝ (Fin n)))
    (D : Fin M → MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) (η : ℝ)
    (X : List (EuclideanSpace ℝ (Fin n))) : ℕ :=
  ∑ j, countIn X (uniqueSection K j \ badRegion K D η j)

end UnionVolEst


