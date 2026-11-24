-- Prove2me | Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_HasFDerivAtOfCurves
-- name    : CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_HasFDerivAtOfCurves
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T23:20:25.775101+00:00
-- url     : https://prove2.me/theorems/11b17ee2-f8e0-479b-afee-d728b0210c9f
-- title:
--   Has FDeriv At Of Curves
-- statement:
--   Definitions and structural lemmas for Has FDeriv At Of Curves, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/HasFDerivAtOfCurves.lean

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_MpFOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology CompanionTheory.ThKR.LL
open scoped Real ContDiff
namespace CompanionTheory.ThKR.Mp.MpG
variable {l : Type} [Fintype l] [DecidableEq l]
end CompanionTheory.ThKR.Mp.MpG
namespace CompanionTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
end CompanionTheory.ThKR.Mp
end


