-- Prove2me | Definitions.Def_UnionVolEst_estBad
-- name    : UnionVolEst_estBad
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:04:43.914198+00:00
-- url     : https://prove2.me/theorems/3fb60094-d20e-413b-891e-550166dfe037
-- title:
--   $\mathrm{Est}_{\mathrm{bad}}=\sum_j Z_j$
-- statement:
--   For a multiset $X$, $\mathrm{Est}_{\mathrm{bad}} = \sum_{j} Z_j$ where $Z_j$ is the number of points of $X$ in the bad part $\hat K_j\cap \mathrm{Bad}_j$ of the $j$-th unique section.
-- source:
--   Banerjee, Bal, Basu, Chakraborty, Chanda, Sarkar, Estimating the Volume of a Union of Convex Bodies, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), §5.1, p.18 (PDF p.20); §5.2.5, p.25 (PDF p.27)

import Mathlib
import Definitions.Def_UnionVolEst_countIn
import Definitions.Def_UnionVolEst_uniqueSection
import Definitions.Def_UnionVolEst_badRegion

namespace UnionVolEst

/-- `Est_bad = Σ_j Z_j`, the number of stored samples lying in the bad parts `K̂_j ∩ Bad_j`
(Banerjee–Bal–Basu–Chakraborty–Chanda–Sarkar, *Estimating the Volume of a Union of Convex Bodies*, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), §5.1, printed p.18, and §5.2.5, printed p.25, PDF pp.20, 27), for a multiset `X`. -/
noncomputable def estBad {n M : ℕ} (K : Fin M → Set (EuclideanSpace ℝ (Fin n)))
    (D : Fin M → MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) (η : ℝ)
    (X : List (EuclideanSpace ℝ (Fin n))) : ℕ :=
  ∑ j, countIn X (uniqueSection K j ∩ badRegion K D η j)

end UnionVolEst


