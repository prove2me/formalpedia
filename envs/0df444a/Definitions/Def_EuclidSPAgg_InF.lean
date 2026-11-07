-- Prove2me | Definitions.Def_EuclidSPAgg_InF
-- name    : EuclidSPAgg_InF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:41:48.869369+00:00
-- url     : https://prove2.me/theorems/483309b3-155b-4478-907b-5da48656ed8c
-- title:
--   The class $\mathcal F_{n,d}$
-- statement:
--   $\mathcal F_{n,d}$ is the class of mechanisms $f:E^n\to E$ that are strategyproof, continuous, anonymous and unanimous. It is the class on which the geometric (structural) part of the paper works.
--
--   **Formalization Note** Continuity is with respect to the product topology on $E^n$, i.e. the Euclidean topology.
-- source:
--   Jia, Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality, arXiv:2609.19394 (held version, sha256 891e6125…), Section 2.1, p.8 (PDF p.10)

import Mathlib
import Definitions.Def_EuclidSPAgg_IsStrategyproof
import Definitions.Def_EuclidSPAgg_IsAnonymous
import Definitions.Def_EuclidSPAgg_IsUnanimous
open RBMSensitivity (E)

namespace EuclidSPAgg

/-- Membership in the class `F_{n,d}` of continuous, anonymous, unanimous, deterministic
strategyproof mechanisms (Jia, *Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality*, arXiv:2609.19394 (held version, sha256 891e6125…), Section 2.1, p.8 (PDF p.10)).

**Formalization Note** "Continuous" is with respect to the product (= Euclidean) topology on
`Fin n → E d`. -/
def InF {n d : ℕ} (f : Mech n d) : Prop :=
  IsStrategyproof f ∧ Continuous f ∧ IsAnonymous f ∧ IsUnanimous f

end EuclidSPAgg


