-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GeneratorExtendsFromGenericFibreValuationRing
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_GeneratorExtendsFromGenericFibreValuationRing
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T15:10:41.14359+00:00
-- url     : https://prove2.me/theorems/1e1161c8-a85e-4e46-b60a-45fc23ddd2fc
-- title:
--   Generator Extends From Generic Fibre Valuation Ring
-- statement:
--   Definitions and structural lemmas for Generator Extends From Generic Fibre Valuation Ring, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/GeneratorExtendsFromGenericFibreValuationRing.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulSecNonzeroOnSpecialFibreStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GlobalTheory.ValGenExtend
def genSec {X : Scheme.{0}} {L : LB X} (t : LB.Gen L) (ht : t.IsGen) : LB.Sec L :=
  ⟨fun i => (t.s i).val, fun i j => by
    have h := congrArg Units.val (ht i j)
    exact h⟩
end GlobalTheory.ValGenExtend


