-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSectionsFam
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSectionsFam
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T14:42:19.367303+00:00
-- url     : https://prove2.me/theorems/3a8092ad-f43e-5a12-b15b-750b1c2fb1aa
-- title:
--   Exists Sections Fam
-- statement:
--   Definitions and structural lemmas for Exists Sections Fam, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSectionsFam.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DenseOfDenseP
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SecCoordBcScaleUnique
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans

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
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild
noncomputable section
namespace GlobalTheory.ZM.FamOf
section Unit
variable {S : Scheme.{0}} (A : Over S)
def unitInv : A ⟶ Over.mk (𝟙 S) ⊗ A := lift (Over.homMk A.hom (by simp)) (𝟙 A)
theorem unitInv_snd : (unitInv A).left ≫ (snd (Over.mk (𝟙 S)) A).left = 𝟙 _ := by
  rw [← Over.comp_left, unitInv, lift_snd]; rfl
def chartPullUnit (L : LB A.left) (k : ℕ) (a : ℤ) (ha : a = k) :
    ChartPull (lbPow L k) (Out.LPow A L a (Over.mk (𝟙 S))) (unitInv A).left :=
  have le : ∀ j : PUnit → L.ι, LB.wchart L (fun _ : PUnit => 𝟙 A.left) j ≤ (unitInv A).left ⁻¹ᵁ
      LB.wchart L (fun _ : Fin 1 => (snd (Over.mk (𝟙 S)) A).left) (fun _ => j PUnit.unit) :=
    fun j y hy => Set.mem_iInter.2 fun _ => by
      have h1 : y ∈ L.U (j PUnit.unit) := Set.mem_iInter.1 hy PUnit.unit
      show ((unitInv A).left ≫ (snd (Over.mk (𝟙 S)) A).left) y ∈ L.U (j PUnit.unit)
      rw [unitInv_snd]; exact h1
  { idx := fun j _ => j PUnit.unit
    le := le
    g := fun y j j' hj hj' => by
      refine (gm_linComb L (fun _ : PUnit => 𝟙 A.left) (fun _ => (k : ℤ)) (𝟙 _) y j j' hj hj').trans
        (Eq.trans ?_ (gm_linComb L (fun _ : Fin 1 => (snd (Over.mk (𝟙 S)) A).left) (fun _ => a) (unitInv A).left y _ _
          (le j hj) (le j' hj')).symm)
      rw [Fintype.prod_unique, Fintype.prod_unique, unitInv_snd, Category.comp_id, ha] }
end Unit
end GlobalTheory.ZM.FamOf
end


