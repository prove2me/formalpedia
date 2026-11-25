-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_UnitsEq
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_UnitsEq
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T17:46:05.350906+00:00
-- url     : https://prove2.me/theorems/e20d86bf-e1af-5d37-a47e-4d08ff76e6f1
-- title:
--   Units Eq
-- statement:
--   Definitions and structural lemmas for Units Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/BaseChangeKernels/UnitsEq.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_PreLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_pullback
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_GtBCPf_iB_isKernel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_GtBCPf_qB_h
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_PullGtPf_isMonHom_of_grpPullback

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
namespace ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
open Semi Geo.Tor PullGtPf
section General
theorem act_le_of_hom {S : Scheme.{0}} {B G T : Over S} [GrpObj G] [GrpObj B] (q : G ⟶ B)
    [IsMonHom q] (i : T ⟶ G) (hk : i ≫ q = toUnit _ ≫ η[B]) (U : B.left.Opens) :
    (snd T G).left ⁻¹ᵁ (q.left ⁻¹ᵁ U) ≤
      (lift (fst T G ≫ i) (snd T G) ≫ μ[G]).left ⁻¹ᵁ (q.left ⁻¹ᵁ U) := by
  have e : (lift (fst T G ≫ i) (snd T G) ≫ μ[G]) ≫ q = snd T G ≫ q := by
    rw [← Hom.mul_def, MonObj.mul_comp, Category.assoc, hk, ← Hom.one_def, MonObj.comp_one,
      _root_.one_mul]
  have e' : (lift (fst T G ≫ i) (snd T G) ≫ μ[G]).left ≫ q.left = (snd T G).left ≫ q.left := by
    rw [← Over.comp_left, e, Over.comp_left]
  intro y hy
  have e₁ := congrArg (fun g => g y) e'
  simp only [Scheme.Hom.comp_apply] at e₁
  exact (congrArg (· ∈ U) e₁).mpr hy
end General
section Torus
variable {S S' : Scheme.{0}} (f : S' ⟶ S) (X : Type) [AddCommGroup X]
end Torus
section Act
variable {S S' : Scheme.{0}} (f : S' ⟶ S) (X : Type) [AddCommGroup X] {G : Over S} [GrpObj G]
abbrev PQ : Over S := Over.mk ((splitTorus S' X ⊗ (Over.pullback f).obj G).hom ≫ f)
def uT : PQ f X (G := G) ⟶ splitTorus S X :=
  Over.homMk ((fst (splitTorus S' X) ((Over.pullback f).obj G)).left ≫ hT f X) (by
    show _ ≫ _ ≫ (splitTorus S X).hom = (splitTorus S' X ⊗ (Over.pullback f).obj G).hom ≫ f
    rw [hT_snd, ← Category.assoc, Over.w (fst (splitTorus S' X) ((Over.pullback f).obj G))])
def vG : PQ f X (G := G) ⟶ G :=
  Over.homMk ((snd (splitTorus S' X) ((Over.pullback f).obj G)).left ≫ pullback.fst G.hom f) (by
    show _ ≫ _ ≫ G.hom = (splitTorus S' X ⊗ (Over.pullback f).obj G).hom ≫ f
    rw [pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ f) (Over.w (snd (splitTorus S' X) ((Over.pullback f).obj G))))
def bm : (splitTorus S' X ⊗ (Over.pullback f).obj G).left ⟶ (splitTorus S X ⊗ G).left :=
  (lift (uT f X) (vG f X)).left
end Act
section Fields
attribute [local instance] SplitExt.free SplitExt.finite
variable {S S' : Scheme.{0}} (f : S' ⟶ S) (E : SplitExt S) {G : Over S} [GrpObj G] (d : E.GtDatum G)
theorem actB_le : ∀ j : (pullExt f E).ChartIdx,
    (snd (splitTorus S' (pullExt f E).X) ((Over.pullback f).obj G)).left ⁻¹ᵁ
        ((qB f d.q).left ⁻¹ᵁ (pullExt f E).chart j) ≤
      (lift (fst (splitTorus S' (pullExt f E).X) ((Over.pullback f).obj G) ≫ iB f E.X d.i)
          (snd (splitTorus S' (pullExt f E).X) ((Over.pullback f).obj G)) ≫
        μ[(Over.pullback f).obj G]).left ⁻¹ᵁ ((qB f d.q).left ⁻¹ᵁ (pullExt f E).chart j) := by
  haveI := d.q_hom
  haveI : IsMonHom (qB f d.q) :=
    isMonHom_of_grpPullback (isGrpPullback_pullback G f) (isGrpPullback_pullback E.B f) d.q
      (qB f d.q) (qB_h f d.q)
  intro j
  exact act_le_of_hom (qB f d.q) (iB f E.X d.i) (iB_isKernel f E.X d.q d.i d.isKernel).w _
end Fields
end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf


