-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsEvenCubicalTrivialisationLiftNilpotent
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsEvenCubicalTrivialisationLiftNilpotent
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T15:00:20.997867+00:00
-- url     : https://prove2.me/theorems/32a455d6-18e6-45ec-bc93-9c6b5f2db3a1
-- title:
--   Exists Even Cubical Trivialisation Lift Nilpotent
-- statement:
--   Definitions and structural lemmas for Exists Even Cubical Trivialisation Lift Nilpotent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsEvenCubicalTrivialisationLiftNilpotent.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsNilpotentOfRd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_EvSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGenLiftOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Theorems.Thm_GlobalTheory_SplitTorus_mul_left_bcMap
import Theorems.Thm_GlobalTheory_TorusCoord_IsPointOf_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.CubeLift
open SplitTorus (bcMap)
section Defect
variable {S : Scheme.{0}} {G H : Over S} [GrpObj G] {i : H ⟶ G}
variable [IsCommMonObj G] [GrpObj H] [IsMonHom i]
end Defect
section Alg
variable {B C U : Type} [CommGroup B] [CommGroup C] [CommGroup U]
end Alg
section Lift
variable {A : Type} [CommRing A] {J : Ideal A} {X : Type} [AddCommGroup X]
  {G : Over (Spec (CommRingCat.of A))} [GrpObj G] [IsCommMonObj G]
  {G₀ : Over (Spec (CommRingCat.of (A ⧸ J)))} [GrpObj G₀] [IsCommMonObj G₀]
  {F : G₀.left ⟶ G.left} {hw : F ≫ G.hom = G₀.hom ≫ red J} {P : CP G} {P₀ : CP G₀}
  {w : LB.Iso P₀.L.L (P.L.L.pull F)} {i : splitTorus _ X ⟶ G} {i₀ : splitTorus _ X ⟶ G₀}
variable (w) in

def Reduces (t : LB.Gen (LB.LinComb P.L.L (K := Fin 2) ![i.left, (1 : splitTorus _ X ⟶ G).left] ![1, -1]))
    (σ₀ : CubTriv P₀.c i₀) : Prop :=
  ∀ (T : Over (Spec (CommRingCat.of (A ⧸ J)))) (z : T.left) (C₀) (C), Good P₀.L.L z C₀ → Good P.L.L z C →
    ∀ W : (T ⟶ G₀) → (T.left.presheaf.stalk z)ˣ, (∀ x, W x = gw w x.left z (C (x.left ≫ F)) (C₀ x.left)) →
      ∀ x : T ⟶ splitTorus _ X, val t (x.left ≫ bcMap (red J) X) z C = W (x ≫ i₀) * (W 1)⁻¹ * val σ₀.s x.left z C₀
def up (T : Over (Spec (CommRingCat.of (A ⧸ J)))) :
    (T ⟶ splitTorus _ X) →* (Over.mk (T.hom ≫ red J) ⟶ splitTorus _ X) :=
  toBaseHom (hw := SplitTorus.bcMap_hom (red J) X) (fun T x y => Over.OverMorphism.ext
    (SplitTorus.mul_left_bcMap (red J) X T x y _ _ rfl rfl).symm) T
end Lift
end GlobalTheory.CubeLift


