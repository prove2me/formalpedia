-- Prove2me | Definitions.Def_EuclidSPAgg_InA
-- name    : EuclidSPAgg_InA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:41:42.8767+00:00
-- url     : https://prove2.me/theorems/c1f81f5d-df2e-4a1f-a6b5-4de89da02bf3
-- title:
--   The class $\mathcal A_{n,d}$
-- statement:
--   $\mathcal S_{n,d}$ is the class of deterministic strategyproof mechanisms $f:E^n\to E$, and $\mathcal A_{n,d}$ is its anonymous subclass: $f\in\mathcal A_{n,d}$ if $f$ is strategyproof and anonymous. No continuity, unanimity or equivariance is required. This is the comparison class of the main optimality theorem.
-- source:
--   Jia, Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality, arXiv:2609.19394 (held version, sha256 891e6125…), Section 2.1, p.8 (PDF p.10)

import Mathlib
import Definitions.Def_EuclidSPAgg_IsStrategyproof
import Definitions.Def_EuclidSPAgg_IsAnonymous
open RBMSensitivity (E)

namespace EuclidSPAgg

/-- Membership in the class `A_{n,d}`, the anonymous subclass of the deterministic strategyproof
class `S_{n,d}` (Jia, *Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality*, arXiv:2609.19394 (held version, sha256 891e6125…), Section 2.1, p.8 (PDF p.10)). -/
def InA {n d : ℕ} (f : Mech n d) : Prop :=
  IsStrategyproof f ∧ IsAnonymous f

end EuclidSPAgg


