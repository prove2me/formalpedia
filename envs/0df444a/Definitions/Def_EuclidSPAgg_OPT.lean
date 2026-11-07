-- Prove2me | Definitions.Def_EuclidSPAgg_OPT
-- name    : EuclidSPAgg_OPT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:40:06.208909+00:00
-- url     : https://prove2.me/theorems/1ee441d3-1604-4b69-afb5-26841c0b103c
-- title:
--   Optimal social cost $\mathrm{OPT}(x)$
-- statement:
--   The **optimal social cost** at a profile $x$ is
--   $$
--   \mathrm{OPT}(x)=\min_{y\in E}\mathrm{SC}(x,y),
--   $$
--   the cost of a geometric median of the reports. The minimum exists because the objective is continuous and coercive.
--
--   **Formalization Note** Written as the real infimum of $\mathrm{SC}(x,\cdot)$ over $E$. The values are nonnegative, so this infimum is the true infimum, which equals the attained minimum.
-- source:
--   Jia, Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality, arXiv:2609.19394 (held version, sha256 891e6125…), Section 2.1, p.8 (PDF p.10)

import Mathlib
import Definitions.Def_EuclidSPAgg_SC
open RBMSensitivity (E)

namespace EuclidSPAgg

/-- The optimal social cost `OPT(x) = min_{y ∈ E} SC(x, y)` (Jia, *Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality*, arXiv:2609.19394 (held version, sha256 891e6125…), Section 2.1, p.8 (PDF p.10)).

**Formalization Note** Written as the real infimum `⨅ y, SC x y`. The family is nonempty and
bounded below by `0`, so this is the true infimum, which the paper notes is attained. -/
noncomputable def OPT {n d : ℕ} (x : Fin n → E d) : ℝ :=
  ⨅ y : E d, SC x y

end EuclidSPAgg


