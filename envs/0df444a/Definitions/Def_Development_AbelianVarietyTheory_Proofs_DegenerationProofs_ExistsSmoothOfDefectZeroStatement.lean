-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSmoothOfDefectZeroStatement
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSmoothOfDefectZeroStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:46:45.093167+00:00
-- url     : https://prove2.me/theorems/c25d163e-f220-4db3-8a42-b4ead617ac08
-- title:
--   Exists Smooth Of Defect Zero Statement
-- statement:
--   Definitions and structural lemmas for Exists Smooth Of Defect Zero Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsSmoothOfDefectZeroStatement.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSmoothOfDefectZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
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


