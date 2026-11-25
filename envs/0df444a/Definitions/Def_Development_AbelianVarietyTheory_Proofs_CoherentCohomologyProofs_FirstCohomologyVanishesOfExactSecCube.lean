-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_FirstCohomologyVanishesOfExactSecCube
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_FirstCohomologyVanishesOfExactSecCube
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T15:45:35.926418+00:00
-- url     : https://prove2.me/theorems/147474ca-f4fc-5c59-9a1b-ffc380e1563e
-- title:
--   First Cohomology Vanishes Of Exact Sec Cube
-- statement:
--   Definitions and structural lemmas for First Cohomology Vanishes Of Exact Sec Cube, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/FirstCohomologyVanishesOfExactSecCube.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CechHOneVanishesOnOpenOfIsAffineOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
namespace GlobalTheory.AbLaw
end GlobalTheory.AbLaw


