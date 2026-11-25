-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_ChartFun
-- name    : GroundTheory_HeightsAndTheta_Heights_Regularisation_ChartFun
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T12:50:42.923931+00:00
-- url     : https://prove2.me/theorems/e05f4c0d-002f-4d0b-b0b5-d6e31727a987
-- title:
--   Chart Fun
-- statement:
--   Definitions and structural lemmas for Chart Fun, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/ChartFun.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StatementsChartBounds
import Theorems.Thm_ReciprocityTheory_AnForm_A_le_tmax
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_ge
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_le
import Theorems.Thm_ReciprocityTheory_AnForm_A_tmax_le

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
open Metric Filter Topology
open ReciprocityTheory.AnForm.A (Mollifier tmax regMax le_tmax tmax_le regMax_ge regMax_le)
noncomputable section
namespace LogLogRegularisation
variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : ReciprocityTheory.AnForm.M.FinHolAtlas D X}
end LogLogRegularisation
end
end GroundTheory.Heights₂.Heights.Regular


