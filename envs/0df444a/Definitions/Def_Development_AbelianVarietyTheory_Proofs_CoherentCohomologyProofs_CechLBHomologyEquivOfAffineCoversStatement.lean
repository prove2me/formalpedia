-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CechLBHomologyEquivOfAffineCoversStatement
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CechLBHomologyEquivOfAffineCoversStatement
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T16:17:35.866809+00:00
-- url     : https://prove2.me/theorems/b543ee7c-2406-58f5-9e38-6708a3f9a92b
-- title:
--   Cech LBHomology Equiv Of Affine Covers Statement
-- statement:
--   Definitions and structural lemmas for Cech LBHomology Equiv Of Affine Covers Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CechLBHomologyEquivOfAffineCoversStatement.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CechLBHomologyEquivOfAffineCovers
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw


