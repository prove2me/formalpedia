-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueModelExtensionOfDefinedAtPoints
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueModelExtensionOfDefinedAtPoints
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:52.523609+00:00
-- url     : https://prove2.me/theorems/d35edca3-5f09-4f64-9eb7-78fdd8db4509
-- title:
--   Exists Unique Model Extension Of Defined At Points
-- statement:
--   Definitions and structural lemmas for Exists Unique Model Extension Of Defined At Points, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsUniqueModelExtensionOfDefinedAtPoints.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLiftOfSchemeTheoreticallyDominant
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
namespace GlobalTheory.SS
section
variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {A A' : Over (Sp K)}
variable [IsDomain R] [IsFractionRing R K]
end
end GlobalTheory.SS


