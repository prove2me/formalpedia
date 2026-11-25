-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_RegularFunctionConstOfFiniteValuesAnyLevel
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_RegularFunctionConstOfFiniteValuesAnyLevel
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T13:57:44.252877+00:00
-- url     : https://prove2.me/theorems/36e7e4ed-5946-5d0d-a970-9b392249180e
-- title:
--   Regular Function Const Of Finite Values Any Level
-- statement:
--   Definitions and structural lemmas for Regular Function Const Of Finite Values Any Level, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/RegularFunctionConstOfFiniteValuesAnyLevel.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_PermutesRefl
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsPeriodDomainParam
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsHolToFibPtAndCompFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLinearEquivLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
namespace GlobalTheory.CompRat
end GlobalTheory.CompRat


