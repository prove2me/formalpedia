-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultPsiEvenOverExtensionFieldStatement
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultPsiEvenOverExtensionFieldStatement
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T15:36:27.628002+00:00
-- url     : https://prove2.me/theorems/75e7a476-1dff-451e-b0dd-199f9983a649
-- title:
--   Tau Bimult Psi Even Over Extension Field Statement
-- statement:
--   Definitions and structural lemmas for Tau Bimult Psi Even Over Extension Field Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TauBimultPsiEvenOverExtensionFieldStatement.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultPsiEvenOverExtensionField
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
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


