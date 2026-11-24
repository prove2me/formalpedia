-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartCutoffParts
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartCutoffParts
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:24:15.903859+00:00
-- url     : https://prove2.me/theorems/d70ed27f-3b13-478f-92d1-85480d4334a2
-- title:
--   Chart Cutoff Parts
-- statement:
--   Definitions and structural lemmas for Chart Cutoff Parts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartCutoffParts.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartCutoffEnergy
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergyCocycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergySwap
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Matrix MeasureTheory Filter Topology
open scoped ComplexOrder
noncomputable section
namespace ChartIntegrationByPartsSymmetry
section Potentials
variable {e : ℕ}
end Potentials
section Cutoff
variable {D : ℕ}
end Cutoff
section GradDens
variable {D : ℕ}
end GradDens
section Chart
variable {n : ℕ}
end Chart
end ChartIntegrationByPartsSymmetry
end
end GroundTheory.Heights₂.Heights


