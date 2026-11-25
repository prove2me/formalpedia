-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PZIntAdd
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_PZIntAdd
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T15:51:07.460279+00:00
-- url     : https://prove2.me/theorems/4095acc1-2ecd-4df7-9ac5-6ff7fc0e9b20
-- title:
--   PZInt Add
-- statement:
--   Definitions and structural lemmas for PZInt Add, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PZIntAdd.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AnalyticResolutionHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StZIntAdd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FourierIntegralBound
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCEqZeroOfEventuallyEqZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PLCurveA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open ReciprocityTheory.AnForm.M Topology
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter


