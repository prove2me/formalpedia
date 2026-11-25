-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqSmulResidueFibreClassOfPullbackEqZero
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqSmulResidueFibreClassOfPullbackEqZero
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T15:52:37.819909+00:00
-- url     : https://prove2.me/theorems/691334c8-dbb7-481b-94b2-8cd0b19a531c
-- title:
--   Eq Smul Residue Fibre Class Of Pullback Eq Zero
-- statement:
--   Definitions and structural lemmas for Eq Smul Residue Fibre Class Of Pullback Eq Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EqSmulResidueFibreClassOfPullbackEqZero.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PreUMono
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreimageCochainRestrictionBijectiveClosedImmersiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CocyclePullbackIffPreimageAffineHomStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SurjectiveDeformationAffineSectionsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.AbCoh
end GlobalTheory.AbCoh


