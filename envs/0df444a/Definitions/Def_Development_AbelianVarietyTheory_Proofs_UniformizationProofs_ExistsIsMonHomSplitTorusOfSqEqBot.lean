-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsIsMonHomSplitTorusOfSqEqBot
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsIsMonHomSplitTorusOfSqEqBot
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T15:28:24.49796+00:00
-- url     : https://prove2.me/theorems/8bcfd2e8-71be-475b-a804-cde4d31c5033
-- title:
--   Exists Is Mon Hom Split Torus Of Sq Eq Bot
-- statement:
--   Definitions and structural lemmas for Exists Is Mon Hom Split Torus Of Sq Eq Bot, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsIsMonHomSplitTorusOfSqEqBot.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LeftEqIffLieVecSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsUnitAddMonoidAlgebraIffOfTwoUniqueSums
import Theorems.Thm_GlobalTheory_SqZero_UnitInChart_map
import Theorems.Thm_GlobalTheory_SqZero_comp_mem_redKer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isMonHom_of_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_spMap_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (epsR IsLieBasis isMonHom_of_mul)
open scoped CategoryTheory.Obj
open AddMonoidAlgebra (single mapDomainAlgHom)
namespace GlobalTheory.TorusDefect
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.SqZero GlobalTheory.Diag
variable {A : Type} [CommRing A] {X Y : Type} [AddCommGroup X] [AddCommGroup Y]
  {C C' : Type} [CommRing C] [Algebra A C] [CommRing C'] [Algebra A C']
variable (A X) in

def univ : sp (AddMonoidAlgebra A X) ⟶ splitTorus (Spec (CommRingCat.of A)) X :=
  ofVal _ (AddMonoidAlgebra.of A X)
def valHom (w : sp C ⟶ splitTorus (Spec (CommRingCat.of A)) X) : Multiplicative X →* C where
  toFun x := charVal w x.toAdd
  map_one' := charVal_zero w
  map_mul' _ _ := charVal_add w _ _
theorem map_mem_map {J : Ideal A} (φ : C →ₐ[A] C') :
    ∀ a ∈ J.map (algebraMap A C), φ a ∈ J.map (algebraMap A C') := fun a ha => by
  have h := Ideal.mem_map_of_mem (φ : C →+* C') ha
  rwa [Ideal.map_map, AlgHom.comp_algebraMap] at h
theorem map_algebraMap_sq {J : Ideal A} (hJ : J ^ 2 = ⊥) : J.map (algebraMap A C) ^ 2 = ⊥ := by rw [← Ideal.map_pow, hJ, Ideal.map_bot]
section Cocycle
variable {G : Over (Spec (CommRingCat.of A))} [GrpObj G] {J : Ideal A}
  {Z : Type} [AddCommGroup Z]
def pull (G : Over (Spec (CommRingCat.of A))) [GrpObj G] (u : X →+ Y) :
    (sp (AddMonoidAlgebra A X) ⟶ G) →* (sp (AddMonoidAlgebra A Y) ⟶ G) :=
  pointsMap G (mapDomainAlgHom A A u)
def pullKer (G : Over (Spec (CommRingCat.of A))) [GrpObj G] (J : Ideal A) (u : X →+ Y) :
    redKer (R := A) G (J.map (algebraMap A (AddMonoidAlgebra A X))) →*
      redKer (R := A) G (J.map (algebraMap A (AddMonoidAlgebra A Y))) :=
  ((pull G u).comp (Subgroup.subtype _)).codRestrict _ fun y =>
    comp_mem_redKer y.2 _ (map_mem_map _)
variable [IsCommMonObj G] [Smooth G.hom] {n : ℕ} {v : Fin n → (epsR A ⟶ G)}
end Cocycle
end GlobalTheory.TorusDefect
namespace GlobalTheory
open SqZero TorusDefect
attribute [local instance] Over.cartesianMonoidalCategory
end GlobalTheory


