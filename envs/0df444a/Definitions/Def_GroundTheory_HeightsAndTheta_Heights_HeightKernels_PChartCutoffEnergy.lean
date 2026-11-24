-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartCutoffEnergy
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartCutoffEnergy
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:39.041075+00:00
-- url     : https://prove2.me/theorems/fc6253fd-8e21-426d-b835-792743dee594
-- title:
--   PChart Cutoff Energy
-- statement:
--   Definitions and structural lemmas for PChart Cutoff Energy, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartCutoffEnergy.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartCutoffEnergy
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartHessCompare
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm Matrix MeasureTheory Filter
open scoped ComplexOrder
noncomputable section
namespace ChartCutoffEnergyAlt
def sqn {D : ℕ} (y : Fin D → ℂ) : ℝ := ∑ i, ‖y i‖ ^ 2
end ChartCutoffEnergyAlt
namespace ChartCutoffEnergyAlt
open ReciprocityTheory.AnForm.A
end ChartCutoffEnergyAlt
namespace ChartCutoffEnergyAlt
open ReciprocityTheory.AnForm.A
end ChartCutoffEnergyAlt
end
end GroundTheory.Heights₂.Heights


