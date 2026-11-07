-- Prove2me | Definitions.Def_UnionVolEst_badRegion
-- name    : UnionVolEst_badRegion
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:03:39.015081+00:00
-- url     : https://prove2.me/theorems/a6c5ff5b-4bd4-468b-b4cd-47f0c5de692c
-- title:
--   Bad region $\mathrm{Bad}_j$ of body $K_j$
-- statement:
--   For bodies $K_j$ with sampling distributions $D_j$ and parameter $\eta$, the **bad region** of $K_j$ is the exceptional region of $D_j$ relative to the uniform distribution $\pi_{K_j}$ on $K_j$:
--   $$
--   \mathrm{Bad}_j := \mathrm{Bad}_\eta(D_j,\pi_{K_j}) \subseteq K_j .
--   $$
--   Its complement $\mathrm{Good}_j = K_j\setminus \mathrm{Bad}_j$ is where the sampler is multiplicatively close to uniform.
--
--   **Formalization Note** $\pi_{K_j}$ is Mathlib's conditional measure `volume[|K j]` $=\mathrm{Vol}(K_j)^{-1}\,\mathrm{Vol}|_{K_j}$ (not `uniformOn`, which is a counting measure). The page's sample space is $K_j$, so the region is intersected with $K_j$; outside $K_j$ the density is unconstrained.
-- source:
--   Banerjee, Bal, Basu, Chakraborty, Chanda, Sarkar, Estimating the Volume of a Union of Convex Bodies, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), §5.1, p.17 (PDF p.19), with Eq. (1), p.11

import Mathlib
import Definitions.Def_UnionVolEst_badSet

open MeasureTheory ProbabilityTheory

namespace UnionVolEst

/-- The bad region `Bad_j` of body `K_j` (Banerjee–Bal–Basu–Chakraborty–Chanda–Sarkar, *Estimating the Volume of a Union of Convex Bodies*, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), §5.1, printed p.17, PDF p.19, with Eq. (1),
printed p.11): the exceptional region `Bad_η(D_j, π_{K_j})` of the sampling distribution `D_j`
relative to the uniform distribution `π_{K_j}` on `K_j`.

**Formalization Note** The uniform distribution on `K_j` is `volume[|K j]` (Mathlib's
conditional measure `(vol K_j)⁻¹ • vol|_{K_j}`), not `uniformOn` (a counting measure). The page's
sample space `S` is `K_j`, so the region is intersected with `K j`: off `K_j` the density is
not constrained and `badSet` alone could contain all of `ℝⁿ \ K_j`. -/
noncomputable def badRegion {n M : ℕ} (K : Fin M → Set (EuclideanSpace ℝ (Fin n)))
    (D : Fin M → Measure (EuclideanSpace ℝ (Fin n))) (η : ℝ) (j : Fin M) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  K j ∩ badSet η (D j) (volume[|K j])

end UnionVolEst


