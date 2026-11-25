-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLelongMassNearSmall
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLelongMassNearSmall
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T02:00:08.241857+00:00
-- url     : https://prove2.me/theorems/d50eaaef-e619-57fd-a9a3-bfa04e0d9613
-- title:
--   PLelong Mass Near Small
-- statement:
--   Definitions and structural lemmas for PLelong Mass Near Small, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLelongMassNearSmall.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongMassNearSmall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegMassNearSmall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarMassNearSmall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_CutOffNear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLelongLimitOnZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceImmersiveGeneral
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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
end GroundTheory.Heights₂.Heights


