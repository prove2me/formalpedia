-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLinearLiftOfIsMonHomPolAVStatement
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLinearLiftOfIsMonHomPolAVStatement
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T17:21:21.047306+00:00
-- url     : https://prove2.me/theorems/ddcd5dbf-678f-57c1-8813-6046358c240b
-- title:
--   Exists Linear Lift Of Is Mon Hom Pol AVStatement
-- statement:
--   Definitions and structural lemmas for Exists Linear Lift Of Is Mon Hom Pol AVStatement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLinearLiftOfIsMonHomPolAVStatement.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLinearLiftOfIsMonHomPolAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct


