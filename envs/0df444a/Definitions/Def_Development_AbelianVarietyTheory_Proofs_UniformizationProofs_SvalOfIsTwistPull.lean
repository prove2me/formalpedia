-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalOfIsTwistPull
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalOfIsTwistPull
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T15:16:06.505591+00:00
-- url     : https://prove2.me/theorems/a6180d2f-5494-4337-be0a-452c2bcf0f03
-- title:
--   Sval Of Is Twist Pull
-- statement:
--   Definitions and structural lemmas for Sval Of Is Twist Pull, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SvalOfIsTwistPull.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_FinrankComplexReal
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
noncomputable section
namespace GlobalTheory.ThetaLin
section Twist
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left}
  {T : Over S} {ψ : T ⊗ A ⟶ T ⊗ A} {m : T ⊗ A ⟶ A} {hm : ψ ≫ snd T A = m} {a b : ℤ}
  {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])}
end Twist
section Transl
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] {T : Over S}
end Transl
end GlobalTheory.ThetaLin
end


