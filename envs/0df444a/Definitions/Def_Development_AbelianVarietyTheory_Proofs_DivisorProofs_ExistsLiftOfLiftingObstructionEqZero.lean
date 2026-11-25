-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLiftOfLiftingObstructionEqZero
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLiftOfLiftingObstructionEqZero
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T15:55:22.316676+00:00
-- url     : https://prove2.me/theorems/0ee40f9d-2e5f-4153-a1b8-9f247a896d1e
-- title:
--   Exists Lift Of Lifting Obstruction Eq Zero
-- statement:
--   Definitions and structural lemmas for Exists Lift Of Lifting Obstruction Eq Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLiftOfLiftingObstructionEqZero.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreimageCochainRestrictionBijectiveClosedImmersiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CocyclePullbackIffPreimageAffineHomStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SurjectiveDeformationAffineSectionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PreUMono
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
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
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace GlobalTheory.AbCoh
end GlobalTheory.AbCoh


