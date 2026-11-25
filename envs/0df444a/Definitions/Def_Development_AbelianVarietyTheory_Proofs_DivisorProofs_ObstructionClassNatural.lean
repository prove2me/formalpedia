-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ObstructionClassNatural
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ObstructionClassNatural
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T15:35:48.312929+00:00
-- url     : https://prove2.me/theorems/566ed0d4-0c8d-4b37-8393-b32ca313eaad
-- title:
--   Obstruction Class Natural
-- statement:
--   Definitions and structural lemmas for Obstruction Class Natural, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ObstructionClassNatural.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PreUMono
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PairFstPreimageRestrictionBijectiveClosedImmersi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CohomologyClassPullbackReductionPairs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CocyclePullbackIffPreimageAffineHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SurjectiveDeformationAffineSections
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
namespace GlobalTheory.AbCoh
end GlobalTheory.AbCoh


