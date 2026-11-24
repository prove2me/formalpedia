-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorsUnit3
-- name    : ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorsUnit3
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T21:44:51.460869+00:00
-- url     : https://prove2.me/theorems/18293e1a-5581-4836-bdb6-25e5165718ad
-- title:
--   Tors Unit3
-- statement:
--   Definitions and structural lemmas for Tors Unit3, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/TorsUnit3.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedDefs
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementK
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsNoPrimeToPTorsion
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_TorInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F WeierstrassCurve
namespace ReciprocityTheory.ChartRestriction.L1
namespace ThreeTorsionChord
open Formalism.ELL.FormalGroupPointsTorsion
variable {K : Type} [NormedField K] [IsUltrametricDist K]
end ThreeTorsionChord
end ReciprocityTheory.ChartRestriction.L1


