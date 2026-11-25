-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueHomExtensionSemiAbelianDvr
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueHomExtensionSemiAbelianDvr
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T00:09:46.360612+00:00
-- url     : https://prove2.me/theorems/65909ad9-8794-428d-af59-d627beb8482b
-- title:
--   Exists Unique Hom Extension Semi Abelian Dvr
-- statement:
--   Definitions and structural lemmas for Exists Unique Hom Extension Semi Abelian Dvr, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsUniqueHomExtensionSemiAbelianDvr.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLiftOfSchemeTheoreticallyDominant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FlatOfIsSchemeTheoreticallyDominantOfFractionRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsGrpObjOfFlatClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsUnitNatCastSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqOneOfPowEqOneOfCompEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LocallyQuasiFiniteOfFiniteGeometricPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenImmersionSpMapOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLiftOfIsReducedOfRangeSubset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory
end GlobalTheory


