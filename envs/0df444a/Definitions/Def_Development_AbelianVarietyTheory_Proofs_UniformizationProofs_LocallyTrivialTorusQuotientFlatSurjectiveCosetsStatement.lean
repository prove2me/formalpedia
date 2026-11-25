-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_LocallyTrivialTorusQuotientFlatSurjectiveCosetsStatement
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_LocallyTrivialTorusQuotientFlatSurjectiveCosetsStatement
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T16:08:26.333891+00:00
-- url     : https://prove2.me/theorems/e9145644-5a46-4a56-b515-99655a6a8f57
-- title:
--   Locally Trivial Torus Quotient Flat Surjective Cosets Statement
-- statement:
--   Definitions and structural lemmas for Locally Trivial Torus Quotient Flat Surjective Cosets Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/LocallyTrivialTorusQuotientFlatSurjectiveCosetsStatement.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_LocallyTrivialTorusQuotientFlatSurjectiveCosets
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU


