-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactCechOneOfH1Zero
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactCechOneOfH1Zero
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T15:36:13.568363+00:00
-- url     : https://prove2.me/theorems/a4b5754b-17e8-443c-a939-8fdf942fb0e9
-- title:
--   Exact Cech One Of H1 Zero
-- statement:
--   Definitions and structural lemmas for Exact Cech One Of H1 Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExactCechOneOfH1Zero.lean

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
namespace GlobalTheory.Cohom
end GlobalTheory.Cohom


