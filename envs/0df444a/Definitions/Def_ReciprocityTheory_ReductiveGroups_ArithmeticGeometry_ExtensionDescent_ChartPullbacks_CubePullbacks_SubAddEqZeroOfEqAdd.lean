-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_CubePullbacks_SubAddEqZeroOfEqAdd
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_CubePullbacks_SubAddEqZeroOfEqAdd
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T14:46:47.421797+00:00
-- url     : https://prove2.me/theorems/e52a53a9-061f-4099-bf57-c427bc8aabb2
-- title:
--   Sub Add Eq Zero Of Eq Add
-- statement:
--   Definitions and structural lemmas for Sub Add Eq Zero Of Eq Add, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/CubePullbacks/SubAddEqZeroOfEqAdd.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_CubePullbacks_CubeMapOfThirdFaceEqPushPtLift
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_GeneratorPullback_PullAlong
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_pullU_res__1e3fd2a0fd54
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_CubePf_inv_comm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_base_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_pullU
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_pullU_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_pullU_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_germ_div
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_germ_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_germ_pull_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_unit_ext

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
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.Out.CubePf
open Semi
open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison (gU unit_ext gU_res gU_pullU gU_pullU_congr gU_pullU_res pullU_res'
  base_eq germ_pull germ_pull_pull germ_div)
section Sym
variable {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
  [IsCommMonObj G] (m : CubeMap G' G)
lemma eSec_inv {S₀ : Scheme.{0}} (H : Over S₀) [GrpObj H] :
    eSec H ≫ (GrpObj.inv (X := H)).left = 𝟙 _ ≫ eSec H := by
  have h : η[H] ≫ GrpObj.inv (X := H) = η[H] := by
    first
    | simp
    | exact GrpObj.one_inv
  rw [Category.id_comp]
  show (η[H] ≫ GrpObj.inv (X := H)).left = η[H].left
  rw [h]
theorem memW_lemma_2 {X Y : Scheme.{0}} (L : LB X) (φ : PUnit.{1} → (Y ⟶ X))
    (j : PUnit.{1} → L.ι) (x : Y) (h : (φ PUnit.unit).base x ∈ L.U (j PUnit.unit)) :
    x ∈ LB.wchart L φ j := by
  show x ∈ (⋂ k, (φ k).base ⁻¹' (L.U (j k) : Set X))
  exact Set.mem_iInter.2 fun k => by cases k; exact h
lemma symLe (L : LB G.left)
    (p : (LB.div ((L.pull m.F).pull (GrpObj.inv (X := G')).left) (L.pull m.F)).ι) :
    (LB.div ((L.pull m.F).pull (GrpObj.inv (X := G')).left) (L.pull m.F)).U p ≤
      m.F ⁻¹ᵁ (LB.div (L.pull (GrpObj.inv (X := G)).left) L).U
        ((fun _ => p.1 PUnit.unit PUnit.unit), p.2 PUnit.unit) := by
  intro y hy
  have h0 : (GrpObj.inv (X := G')).left.base y ∈ (L.pull m.F).U (p.1 PUnit.unit) :=
    LB.wchart_le (L.pull m.F) (fun _ : PUnit => (GrpObj.inv (X := G')).left) p.1 PUnit.unit hy.1
  have h1 : m.F.base ((GrpObj.inv (X := G')).left.base y) ∈ L.U (p.1 PUnit.unit PUnit.unit) :=
    LB.wchart_le L (fun _ : PUnit => m.F) (p.1 PUnit.unit) PUnit.unit h0
  have h2 : m.F.base y ∈ L.U (p.2 PUnit.unit) :=
    LB.wchart_le L (fun _ : PUnit => m.F) p.2 PUnit.unit hy.2
  have h3 : (GrpObj.inv (X := G)).left.base (m.F.base y) ∈ L.U (p.1 PUnit.unit PUnit.unit) := by
    rw [← base_eq (inv_comm m) y]
    exact h1
  exact (show m.F.base y ∈ LB.wchart L (fun _ : PUnit => (GrpObj.inv (X := G)).left)
      (fun _ => p.1 PUnit.unit PUnit.unit) ⊓ L.U (p.2 PUnit.unit) from
    ⟨memW_lemma_2 L (fun _ : PUnit => (GrpObj.inv (X := G)).left)
      (fun _ => p.1 PUnit.unit PUnit.unit) (m.F.base y) h3, h2⟩)
def symIso (L : LB G.left) (w₀ : LB.Iso L (L.pull (GrpObj.inv (X := G)).left)) :
    LB.Iso (L.pull m.F) ((L.pull m.F).pull (GrpObj.inv (X := G')).left) where
  s := fun p => res (symLe m L p) (pullU m.F _ (w₀.s ((fun _ => p.1 PUnit.unit PUnit.unit),
    p.2 PUnit.unit)))
end Sym
end ReciprocityTheory.ChartRestriction.G.Out.CubePf


