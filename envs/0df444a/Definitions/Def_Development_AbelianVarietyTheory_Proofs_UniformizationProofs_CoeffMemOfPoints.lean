-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CoeffMemOfPoints
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CoeffMemOfPoints
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T16:29:41.940177+00:00
-- url     : https://prove2.me/theorems/06716dc5-1869-4a40-a022-0bb44465aaf4
-- title:
--   Coeff Mem Of Points
-- statement:
--   Definitions and structural lemmas for Coeff Mem Of Points, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/CoeffMemOfPoints.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompRedIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUnitCoboundaryOfMulCocycleStatement
import Theorems.Thm_GlobalTheory_UU_CubWeil_comp
import Theorems.Thm_GlobalTheory_UU_IsCPMap_comp
import Theorems.Thm_GlobalTheory_WeilCube_IsRatio_comp
import Theorems.Thm_GlobalTheory_coe_unitsAddMonoidAlgebraEquiv
import Theorems.Thm_GlobalTheory_mem_coactionWeightSpace
import Theorems.Thm_GlobalTheory_trivialCoaction_apply
import Theorems.Thm_GlobalTheory_tupleCoface_last
import Theorems.Thm_GlobalTheory_tupleCoface_zero
import Theorems.Thm_GlobalTheory_tupleContraction_apply
import Theorems.Thm_P2M_GlobalTheory_hochschildD__trivialCoaction_d0af9f793cf0
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.coe_unitsAddMonoidAlgebraEquiv
attribute [local simp] GlobalTheory.mem_coactionWeightSpace
attribute [local simp] GlobalTheory.trivialCoaction_apply
attribute [local simp] GlobalTheory.tupleCoface_last
attribute [local simp] GlobalTheory.tupleCoface_zero
attribute [local simp] GlobalTheory.tupleContraction_apply
attribute [local simp] P2M_GlobalTheory_hochschildD__trivialCoaction_d0af9f793cf0


set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU GlobalTheory.UU.RingPoint
noncomputable section
namespace GlobalTheory.UU.UnitCob
section Alg
variable {B C : Type} [CommRing B] [CommRing C] {M N : Type} [AddCommGroup M] [AddCommGroup N]
def ev (κ : B →+* C) (c : Multiplicative M →* Cˣ) : AddMonoidAlgebra B M →+* C :=
  AddMonoidAlgebra.liftNCRingHom κ ((Units.coeHom C).comp c) fun _ _ => Commute.all _ _
def pair (c : Multiplicative M →* Cˣ) (c' : Multiplicative N →* Cˣ) : Multiplicative (M × N) →* Cˣ :=
  MonoidHom.mk' (fun p => c (Multiplicative.ofAdd p.toAdd.1) * c' (Multiplicative.ofAdd p.toAdd.2)) fun p q => by
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, ofAdd_add, map_mul]
    exact _root_.mul_mul_mul_comm _ _ _ _
def mon (B : Type) [CommRing B] (s : M →+ N) : Multiplicative M →* (AddMonoidAlgebra B N)ˣ :=
  ((AddMonoidAlgebra.of B N).comp (AddMonoidHom.toMultiplicative s)).toHomUnits
end Alg
section Geo
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {Y : Over S}
def ev₁ {Z : Over S} (t : Z ⟶ splitTorus S X) (y : Z ⟶ Y) : AddMonoidAlgebra Γ(Y.left, ⊤) X →+* Γ(Z.left, ⊤) :=
  ev y.left.appTop.hom (splitTorusPointsEquiv S X Z t)
def ev₂ {Z : Over S} (t t' : Z ⟶ splitTorus S X) (y : Z ⟶ Y) :
    AddMonoidAlgebra Γ(Y.left, ⊤) (X × X) →+* Γ(Z.left, ⊤) :=
  ev y.left.appTop.hom (pair (splitTorusPointsEquiv S X Z t) (splitTorusPointsEquiv S X Z t'))
abbrev pl {Z W : Scheme.{0}} (r : Z ⟶ W) (u : Γ(W, ⊤)ˣ) : Γ(Z, ⊤)ˣ := Units.map r.appTop.hom.toMonoidHom u
end Geo
section Red
variable {A : Type} [CommRing A] (J : Ideal A) {X : Type} [AddCommGroup X] {Y : Over (Spec (CommRingCat.of A))}
end Red
end GlobalTheory.UU.UnitCob
end


