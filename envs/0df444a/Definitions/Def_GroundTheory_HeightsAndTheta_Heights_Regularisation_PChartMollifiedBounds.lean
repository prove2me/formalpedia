-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PChartMollifiedBounds
-- name    : GroundTheory_HeightsAndTheta_Heights_Regularisation_PChartMollifiedBounds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:36:29.914586+00:00
-- url     : https://prove2.me/theorems/ecc32f62-12d9-40fb-882a-109bc83c93dd
-- title:
--   PChart Mollified Bounds
-- statement:
--   Definitions and structural lemmas for PChart Mollified Bounds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PChartMollifiedBounds.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StatementsChartBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StatementsTruncPsh
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMoll
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Regular
open Metric Filter Topology MeasureTheory Set
open ReciprocityTheory.AnForm.A (IsPsh Mollifier molli coordDiv limsupExt polyMax shrink)
noncomputable section
end
end GroundTheory.Heights₂.Heights.Regular


