-- Prove2me | Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsSubgroupHolds
-- name    : Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsSubgroupHolds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:57:42.242642+00:00
-- url     : https://prove2.me/theorems/4f79a14d-63fa-4d38-be8d-1420b79fe1d3
-- title:
--   Formal Group Points Subgroup Holds
-- statement:
--   Definitions and structural lemmas for Formal Group Points Subgroup Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsSubgroupHolds.lean

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsTorsionFree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
namespace Formalism.ELL.FormalGroupPointsSubgroup
open WeierstrassCurve Polynomial
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
end Formalism.ELL.FormalGroupPointsSubgroup
namespace Formalism.ELL
open WeierstrassCurve
end Formalism.ELL


