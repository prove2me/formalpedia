-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartDiffEnergy
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartDiffEnergy
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:48.501969+00:00
-- url     : https://prove2.me/theorems/0fc04448-0eb8-4d73-aa64-4a87de20022c
-- title:
--   PChart Diff Energy
-- statement:
--   Definitions and structural lemmas for PChart Diff Energy, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartDiffEnergy.lean

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
open scoped ComplexOrder
noncomputable section
namespace ChartEnergyDifferenceBound
end ChartEnergyDifferenceBound
open ChartIntegrationByPartsSymmetry ChartEnergyDifferenceBound
end
end GroundTheory.Heights₂.Heights


