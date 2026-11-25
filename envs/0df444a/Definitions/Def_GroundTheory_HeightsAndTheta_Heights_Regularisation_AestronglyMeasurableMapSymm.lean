-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_AestronglyMeasurableMapSymm
-- name    : GroundTheory_HeightsAndTheta_Heights_Regularisation_AestronglyMeasurableMapSymm
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T14:16:42.036083+00:00
-- url     : https://prove2.me/theorems/690c8994-ecfa-4ead-ad6f-83128c3d80fa
-- title:
--   Aestrongly Measurable Map Symm
-- statement:
--   Definitions and structural lemmas for Aestrongly Measurable Map Symm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/AestronglyMeasurableMapSymm.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_ChartMongeAmpereL1Hypotheses
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
open MeasureTheory Filter Topology Set
open scoped ENNReal
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot maMeasure ChartPartition locDens)
open GroundTheory.Heights₂.Heights.Regular (PotentialCharts)
noncomputable section
namespace ChartMongeAmpereL1Measure
end ChartMongeAmpereL1Measure
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular


