-- Prove2me | Definitions.Def_EuclidSPAgg_Supplement_medianRatioSup
-- name    : EuclidSPAgg_Supplement_medianRatioSup
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:44:43.096109+00:00
-- url     : https://prove2.me/theorems/cbbd7d03-461e-44d7-b4e7-228aa5e4ce4e
-- title:
--   Large-population median benchmark $C_d=\sup_{n\ge2}R_{n,d}$, display (2.2)
-- statement:
--   For a dimension $d$, let $R_{n,d}=\mathrm{AR}(\mathrm{CM}_{n,d})$ be the approximation ratio of the coordinate-wise median on $n$ agents. The **large-population median benchmark** is
--   $$
--   C_d:=\sup_{n\ge2}R_{n,d}.
--   $$
--
--   Theorem 9.3 shows that $C_d$ is the limit of the optimal deterministic strategyproof ratio as the population grows.
--
--   **Formalization Note** The supremum is taken in $[0,\infty]$ and includes the two-agent term, as in (2.2).
-- source:
--   Jia, Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality, arXiv:2609.19394 (held version, sha256 891e6125…), display (2.2), p.9 (PDF p.11)

import Mathlib
import Definitions.Def_EuclidSPAgg_medianRatio
open RBMSensitivity (E)

namespace EuclidSPAgg.Supplement

/-- The large-population median benchmark `C_d := sup_{n ≥ 2} R_{n,d}`, with
`R_{n,d} = AR(CM_{n,d})` (Jia, *Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality*, arXiv:2609.19394 (held version, sha256 891e6125…), display (2.2), p.9 (PDF p.11)).

**Formalization Note** The supremum is in `ℝ≥0∞` over `n ≥ 2` (the two-agent term included, as in
(2.2)); `R_{n,d}` is the published `medianRatio n d`. -/
noncomputable def medianRatioSup (d : ℕ) : ENNReal :=
  ⨆ (n : ℕ) (_ : 2 ≤ n), medianRatio n d

end EuclidSPAgg.Supplement


