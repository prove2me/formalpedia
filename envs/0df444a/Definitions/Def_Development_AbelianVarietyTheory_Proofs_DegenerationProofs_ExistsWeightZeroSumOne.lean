-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsWeightZeroSumOne
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsWeightZeroSumOne
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T16:25:24.445029+00:00
-- url     : https://prove2.me/theorems/9461d83d-74ba-4b34-8ada-63be42393c5f
-- title:
--   Exists Weight Zero Sum One
-- statement:
--   Definitions and structural lemmas for Exists Weight Zero Sum One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsWeightZeroSumOne.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsAffineSplitTorusLeft
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorusStableAffineOpenFunctionsWeightGraded
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Theorems.Thm_GlobalTheory_UU_IsWt_add
import Theorems.Thm_GlobalTheory_UU_isWt_zero

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
open GlobalTheory.ZJ
namespace GlobalTheory.LocalWeightUnits
variable {S : Scheme.{0}} {H : Over S} [GrpObj H] {X : Type} [AddCommGroup X] {i : splitTorus S X ⟶ H}
def wtSpace (i : splitTorus S X ⟶ H) (V : H.left.Opens) (χ : X) : AddSubgroup Γ(H.left, V) where
  carrier := {u | GlobalTheory.UU.IsWt i V u χ}
  zero_mem' := GlobalTheory.UU.isWt_zero χ
  add_mem' := GlobalTheory.UU.IsWt.add
  neg_mem' := fun {u} hu Z t g h₁ h₂ => by rw [map_neg, map_neg, hu Z t g h₁ h₂, mul_neg]
end GlobalTheory.LocalWeightUnits


