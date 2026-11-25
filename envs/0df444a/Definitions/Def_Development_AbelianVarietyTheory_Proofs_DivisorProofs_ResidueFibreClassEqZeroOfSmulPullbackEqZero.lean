-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ResidueFibreClassEqZeroOfSmulPullbackEqZero
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ResidueFibreClassEqZeroOfSmulPullbackEqZero
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T15:50:14.361746+00:00
-- url     : https://prove2.me/theorems/66d1c2a4-b0d0-4bb4-9e53-a33707ff9bc6
-- title:
--   Residue Fibre Class Eq Zero Of Smul Pullback Eq Zero
-- statement:
--   Definitions and structural lemmas for Residue Fibre Class Eq Zero Of Smul Pullback Eq Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ResidueFibreClassEqZeroOfSmulPullbackEqZero.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PreUMono
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PairFstPreimageRestrictionBijectiveClosedImmersiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SurjectiveDeformationAffineSectionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CohomologyClassPullbackReductionPairsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.AbCoh
end GlobalTheory.AbCoh


