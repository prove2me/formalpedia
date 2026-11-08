-- Prove2me | Definitions.Def_GaussianSweep_bCorr
-- name    : GaussianSweep_bCorr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:53:03.86646+00:00
-- url     : https://prove2.me/theorems/5f5d00e5-4b3a-4814-8d93-e3faa27703cc
-- title:
--   $b(r) = (3r^2-1)/2$
-- statement:
--   For a real $r$ put
--   $$
--   b(r) = \frac{3r^2 - 1}{2}.
--   $$
--   For $r \in (0,1)$ this is the correlation between two neighbor coordinates of the ideal 3-star at correlation $r$, and $b(r) \in (-\tfrac12, 1)$.
--
--   **Formalization Note** Defined for every real $r$; the results using it assume $0 < r < 1$.
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Eq. (8.1), p.45 (PDF p.47)

import Mathlib

namespace GaussianSweep

/-- The neighbor-pair correlation `b(r) = (3r² − 1)/2` of the ideal 3-star at correlation `r`
(Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Eq. (8.1), p.45 (PDF p.47)).

**Formalization Note** Defined for every real `r`; the paper uses it for `0 < r < 1`, and the
lemmas carry that hypothesis. -/
noncomputable def bCorr (r : ℝ) : ℝ := (3 * r ^ 2 - 1) / 2

end GaussianSweep


