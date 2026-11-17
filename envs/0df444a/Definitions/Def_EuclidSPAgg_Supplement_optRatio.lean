-- Prove2me | Definitions.Def_EuclidSPAgg_Supplement_optRatio
-- name    : EuclidSPAgg_Supplement_optRatio
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:43:38.995507+00:00
-- url     : https://prove2.me/theorems/1c16fe6d-c5af-4d79-b0b0-f8ed33924c97
-- title:
--   Optimal strategyproof ratio $a_{n,d}$, display (2.2)
-- statement:
--   For $n$ agents in $\mathbb R^d$, the **optimal deterministic strategyproof ratio** is
--   $$
--   a_{n,d}:=\inf_{f\in\mathcal S_{n,d}}\mathrm{AR}(f),
--   $$
--   the infimum of the approximation ratio over all deterministic strategyproof mechanisms $f:(\mathbb R^d)^n\to\mathbb R^d$, with no anonymity, continuity or unanimity requirement.
--
--   It is the quantity whose large-population limit Theorem 9.3 determines.
--
--   **Formalization Note** The infimum is taken in $[0,\infty]$; the paper uses $a_{n,d}$ for $n\ge2$.
-- source:
--   Jia, Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality, arXiv:2609.19394 (held version, sha256 891e6125…), display (2.2), p.9 (PDF p.11)

import Mathlib
import Definitions.Def_EuclidSPAgg_IsStrategyproof
import Definitions.Def_EuclidSPAgg_AR
open RBMSensitivity (E)

namespace EuclidSPAgg.Supplement

/-- The optimal ratio among deterministic strategyproof mechanisms,
`a_{n,d} := inf_{f ∈ S_{n,d}} AR(f)` (Jia, *Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality*, arXiv:2609.19394 (held version, sha256 891e6125…), display (2.2), p.9 (PDF p.11)).

**Formalization Note** The infimum is in `ℝ≥0∞` over all maps `f : (ℝᵈ)ⁿ → ℝᵈ` satisfying
strategyproofness (2.1) (the published `IsStrategyproof`), with the published `AR`; no anonymity,
continuity or unanimity is required. The paper uses it for `n ≥ 2`. -/
noncomputable def optRatio (n d : ℕ) : ENNReal :=
  ⨅ (f : Mech n d) (_ : IsStrategyproof f), AR f

end EuclidSPAgg.Supplement


