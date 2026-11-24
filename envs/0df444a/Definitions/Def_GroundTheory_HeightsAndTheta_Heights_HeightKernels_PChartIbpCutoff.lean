-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartIbpCutoff
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartIbpCutoff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:35:47.030242+00:00
-- url     : https://prove2.me/theorems/5ea732bc-df84-4bec-8e70-ff35807bdd19
-- title:
--   PChart Ibp Cutoff
-- statement:
--   Definitions and structural lemmas for PChart Ibp Cutoff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartIbpCutoff.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartIbpSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartCutoffParts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergyIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PHermFormCompare
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Matrix MeasureTheory Filter Topology
open ChartIntegrationByPartsSymmetry
open scoped ComplexOrder
noncomputable section
namespace ChartIntegrationByPartsCutoff
variable {n : ℕ}
def outer (n k : ℕ) : Set (Fin (n + 1) → ℂ) := {y | ((k : ℝ) + 1) ^ 2 ≤ ∑ i, ‖y i‖ ^ 2}
end ChartIntegrationByPartsCutoff
end
end GroundTheory.Heights₂.Heights


