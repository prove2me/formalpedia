-- Prove2me | Definitions.Def_UnionVolEst_goodVolume
-- name    : UnionVolEst_goodVolume
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:04:33.427394+00:00
-- url     : https://prove2.me/theorems/5978eee3-514c-4a7f-826f-24ad39f403a9
-- title:
--   Volume of the good parts $F_0' = \sum_j \mathrm{Vol}(\hat K_j\setminus\mathrm{Bad}_j)$ (Eq. (2))
-- statement:
--   The total volume of the good parts of the unique sections is
--   $$
--   F_0' := \mathrm{Vol}\Big(\bigcup_j (\hat K_j \setminus \mathrm{Bad}_j)\Big) = \sum_{j=1}^M \mathrm{Vol}(\hat K_j\setminus \mathrm{Bad}_j).
--   $$
--   Claim 9 shows that $F_0'$ is within a factor $1-\varepsilon/32$ of $F_0$, so it suffices to estimate $F_0'$.
--
--   **Formalization Note** Defined by the sum (the page's second expression), each term read as a real number.
-- source:
--   Banerjee, Bal, Basu, Chakraborty, Chanda, Sarkar, Estimating the Volume of a Union of Convex Bodies, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), §5.1, Eq. (2), p.17 (PDF p.19)

import Mathlib
import Definitions.Def_UnionVolEst_uniqueSection
import Definitions.Def_UnionVolEst_badRegion

open MeasureTheory

namespace UnionVolEst

/-- The total volume of the good parts, Eq. (2) (Banerjee–Bal–Basu–Chakraborty–Chanda–Sarkar, *Estimating the Volume of a Union of Convex Bodies*, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), §5.1, printed p.17, PDF p.19):
`F′₀ := Vol(⋃_j (K̂_j \ Bad_j)) = Σ_j Vol(K̂_j \ Bad_j)`.

**Formalization Note** Defined by the sum (the page's second expression; the unique sections are
pairwise disjoint, so it equals the volume of the union), each term read in `ℝ` by
`ENNReal.toReal` (finite whenever `K_j` has finite volume, as assumed by every result). -/
noncomputable def goodVolume {n M : ℕ} (K : Fin M → Set (EuclideanSpace ℝ (Fin n)))
    (D : Fin M → Measure (EuclideanSpace ℝ (Fin n))) (η : ℝ) : ℝ :=
  ∑ j, (volume (uniqueSection K j \ badRegion K D η j)).toReal

end UnionVolEst


