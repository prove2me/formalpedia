-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PowEqOneOfPush
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PowEqOneOfPush
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T19:44:58.660409+00:00
-- url     : https://prove2.me/theorems/735427b6-a06b-4dca-a529-7f0b45749f7c
-- title:
--   Pow Eq One Of Push
-- statement:
--   Definitions and structural lemmas for Pow Eq One Of Push, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PowEqOneOfPush.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSecOfLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorsionEqOneOfTranslationKeepsRatios
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ThetaBaseChange
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange GlobalTheory.ThetaScalar
section Bundles
variable {Y Y' X X' N N' : Scheme.{0}} {L : LB X} {L' : LB X'} {M : LB N} {M' : LB N'}
end Bundles
section Geometry
variable {S S' W : Scheme.{0}} {g : S' ⟶ S} {t : W ⟶ S} {t' : W ⟶ S'}
variable {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {Φ : A'.left ⟶ A.left}
end Geometry
section Theta
variable {S S' W : Scheme.{0}} {g : S' ⟶ S} {t : W ⟶ S} {t' : W ⟶ S'}
  {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {Φ : A'.left ⟶ A.left} {L : LB A.left} {L' : LB A'.left}
def Moved (v : LB.Iso L' (L.pull Φ)) (ω : (Over.mk t ⊗ A).left ⟶ (Over.mk t' ⊗ A').left) {k : ℤ}
    (s' : LB.Sec (LPow A' L' k (Over.mk t'))) (s : LB.Sec (LPow A L k (Over.mk t))) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ (Over.mk t ⊗ A).left) (z : Z) (i : L.ι) (i' : L'.ι),
    (snd (Over.mk t) A).left (r z) ∈ L.U i → (snd (Over.mk t') A').left (ω (r z)) ∈ L'.U i' →
    powVal (L := L) (g := (snd (Over.mk t) A).left) s r z i =
      (gw v ((r ≫ ω) ≫ (snd (Over.mk t') A').left) z i i' ^ k).val *
        powVal (L := L') (g := (snd (Over.mk t') A').left) s' (r ≫ ω) z i'
end Theta
section Sections
variable {S S' W : Scheme.{0}} {t : W ⟶ S} {t' : W ⟶ S'}
  {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {Φ : A'.left ⟶ A.left} {L : LB A.left} {L' : LB A'.left}
  {ω : (Over.mk t ⊗ A).left ⟶ (Over.mk t' ⊗ A').left} {Y Y' N N' V V' : Scheme.{0}} {M : LB N} {M' : LB N'}
end Sections
end GlobalTheory.ThetaBaseChange


