-- Prove2me | Definitions.Def_EuclidSPAgg_medianRatio
-- name    : EuclidSPAgg_medianRatio
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:43:19.339514+00:00
-- url     : https://prove2.me/theorems/ca6eb7c6-9875-425f-92e2-4c4009fb948b
-- title:
--   Ratio of the median, $R_{n,d}=\mathrm{AR}(\mathrm{CM}_{n,d})$
-- statement:
--   $R_{n,d}:=\mathrm{AR}(\mathrm{CM}_{n,d})$ is the approximation ratio of the coordinate-wise median for $n$ agents in $\mathbb R^d$. By the paper's footnote 1 every orthonormal basis and every fixed choice of middle ranks gives the same value; the definition uses the standard basis and the lower middle rank.
-- source:
--   Jia, Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality, arXiv:2609.19394 (held version, sha256 891e6125…), Section 2.1, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_EuclidSPAgg_CM
import Definitions.Def_EuclidSPAgg_AR
open RBMSensitivity (E)

namespace EuclidSPAgg

/-- The ratio of the coordinate-wise median, `R_{n,d} := AR(CM_{n,d})` (Jia, *Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality*, arXiv:2609.19394 (held version, sha256 891e6125…), Section 2.1, p.9
(PDF p.11)). -/
noncomputable def medianRatio (n d : ℕ) : ENNReal :=
  AR (CM n d)

end EuclidSPAgg


