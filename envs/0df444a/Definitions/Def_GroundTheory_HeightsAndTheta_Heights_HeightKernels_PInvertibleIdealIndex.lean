-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PInvertibleIdealIndex
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_PInvertibleIdealIndex
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:31.41365+00:00
-- url     : https://prove2.me/theorems/f5fce081-3e5d-480d-8a0b-91ef38d084a2
-- title:
--   PInvertible Ideal Index
-- statement:
--   Definitions and structural lemmas for PInvertible Ideal Index, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PInvertibleIdealIndex.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsInvertibleIdealIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsOrderIdealIndexExtension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLocallyPrincipalCoprime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ExistsSmulMemOfSpanEqTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesLineDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open NumberField
noncomputable section
namespace InvertibleIdealIndexAlt
variable {L : Type} [Field L]
def mulBy (c : L) : L →+ L := AddMonoidHom.mulLeft c
end InvertibleIdealIndexAlt
end
end GroundTheory.Heights₂.Heights


