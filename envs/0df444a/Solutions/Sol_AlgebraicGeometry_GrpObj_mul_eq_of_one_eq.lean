-- Prove2me | solution 1 for AlgebraicGeometry.GrpObj.mul_eq_of_one_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/330347e6-daba-5adc-912c-b0158f027050

import Mathlib
import Theorems.Thm_AlgebraicGeometry_exists_eq_pullback_snd_comp_of_isProper
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_GrpObj_mul_eq_of_one_eq

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry"

theorem solution {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of K)) [IsProper x] [IsIntegral X]
    [IsReduced (CategoryTheory.Limits.pullback x x)]
    (G₁ G₂ : GrpObj (Over.mk x)) (h : G₁.one = G₂.one) : G₁.mul = G₂.mul := by
  classical

  let θ : Over.mk x ⊗ Over.mk x ⟶ Over.mk x :=
    lift G₁.mul (G₂.mul ≫ G₂.inv) ≫ G₂.mul

  let sliceR : Over.mk x ⟶ Over.mk x ⊗ Over.mk x := lift (𝟙 _) (toUnit _ ≫ G₂.one)
  let sliceL : Over.mk x ⟶ Over.mk x ⊗ Over.mk x := lift (toUnit _ ≫ G₂.one) (𝟙 _)

  have h1R : sliceR ≫ G₁.mul = 𝟙 (Over.mk x) := by
    rw [show sliceR = lift (𝟙 _) (toUnit _ ≫ G₁.one) by rw [h]]
    letI : MonObj (Over.mk x) := G₁.toMonObj
    exact MonObj.lift_comp_one_right _ _
  have h2R : sliceR ≫ G₂.mul = 𝟙 (Over.mk x) := by
    letI : MonObj (Over.mk x) := G₂.toMonObj
    exact MonObj.lift_comp_one_right _ _
  have h1L : sliceL ≫ G₁.mul = 𝟙 (Over.mk x) := by
    rw [show sliceL = lift (toUnit _ ≫ G₁.one) (𝟙 _) by rw [h]]
    letI : MonObj (Over.mk x) := G₁.toMonObj
    exact MonObj.lift_comp_one_left _ _
  have h2L : sliceL ≫ G₂.mul = 𝟙 (Over.mk x) := by
    letI : MonObj (Over.mk x) := G₂.toMonObj
    exact MonObj.lift_comp_one_left _ _
  have hR : sliceR ≫ θ = toUnit _ ≫ G₂.one := by
    have e1 : sliceR ≫ θ
        = lift (sliceR ≫ G₁.mul) (sliceR ≫ (G₂.mul ≫ G₂.inv)) ≫ G₂.mul := by
      rw [show sliceR ≫ θ = (sliceR ≫ lift G₁.mul (G₂.mul ≫ G₂.inv)) ≫ G₂.mul by
        rw [Category.assoc], comp_lift]
    rw [e1, h1R, show sliceR ≫ (G₂.mul ≫ G₂.inv) = G₂.inv by
      rw [← Category.assoc, h2R, Category.id_comp]]
    letI : GrpObj (Over.mk x) := G₂
    exact GrpObj.right_inv _
  have hL : sliceL ≫ θ = toUnit _ ≫ G₂.one := by
    have e1 : sliceL ≫ θ
        = lift (sliceL ≫ G₁.mul) (sliceL ≫ (G₂.mul ≫ G₂.inv)) ≫ G₂.mul := by
      rw [show sliceL ≫ θ = (sliceL ≫ lift G₁.mul (G₂.mul ≫ G₂.inv)) ≫ G₂.mul by
        rw [Category.assoc], comp_lift]
    rw [e1, h1L, show sliceL ≫ (G₂.mul ≫ G₂.inv) = G₂.inv by
      rw [← Category.assoc, h2L, Category.id_comp]]
    letI : GrpObj (Over.mk x) := G₂
    exact GrpObj.right_inv _

  have hy₀ : (G₂.one).left ≫ x = 𝟙 (Spec (CommRingCat.of K)) := by
    have hw := Over.w (G₂.one)
    simp only [Over.mk_hom, Over.tensorUnit_hom] at hw
    exact hw
  have hcontr : pullback.lift (𝟙 X) (x ≫ (G₂.one).left)
      (show 𝟙 X ≫ x = (x ≫ (G₂.one).left) ≫ x by
        rw [Category.id_comp, Category.assoc]
        exact (Category.comp_id x).symm.trans (congrArg (x ≫ ·) hy₀.symm)) ≫ θ.left
      = x ≫ (G₂.one).left := by
    have hc := congrArg CommaMorphism.left hR
    simp only [Over.comp_left, Over.toUnit_left, Over.mk_left, Over.mk_hom] at hc
    convert hc using 2
    rfl
    rfl
    rfl
    rfl
  obtain ⟨g, hg⟩ := AlgebraicGeometry.exists_eq_pullback_snd_comp_of_isProper
    x x x θ.left (by simpa using θ.w) (G₂.one).left hy₀ (G₂.one).left hcontr

  have hgval : g = x ≫ (G₂.one).left := by
    have hsl := congrArg CommaMorphism.left hL
    simp only [Over.comp_left, Over.toUnit_left, Over.mk_left, Over.mk_hom] at hsl
    have hsnd : (sliceL.left) ≫ pullback.snd x x = 𝟙 X := by
      show (CartesianMonoidalCategory.lift (toUnit (Over.mk x) ≫ G₂.one)
        (𝟙 (Over.mk x))).left ≫ pullback.snd x x = 𝟙 X
      rw [Over.lift_left]
      exact pullback.lift_snd _ _ _
    have hstep : sliceL.left ≫ pullback.snd x x ≫ g = sliceL.left ≫ θ.left :=
      congrArg (fun t => sliceL.left ≫ t) hg.symm
    have hlast : sliceL.left ≫ θ.left = x ≫ (G₂.one).left := by
      simpa only [sliceL, Over.lift_left, Over.toUnit_left, Over.id_left,
        Over.mk_left, Over.mk_hom] using hsl
    exact (Category.id_comp g).symm.trans
      (((congrArg (fun t => t ≫ g) hsnd).symm.trans (Category.assoc _ _ _)).trans
        (hstep.trans hlast))

  have hθ : θ = toUnit _ ≫ G₂.one := by
    apply Over.OverMorphism.ext
    rw [hg, hgval]
    simp only [Over.comp_left, Over.toUnit_left]
    change pullback.snd x x ≫ x ≫ (G₂.one).left
      = (pullback.fst x x ≫ x) ≫ (G₂.one).left
    rw [Category.assoc]
    exact (pullback.condition_assoc _).symm

  letI : GrpObj (Over.mk x) := G₂
  have hcancel := (GrpObj.lift_inv_right_eq G₁.mul G₂.mul (toUnit _ ≫ G₂.one)).mp hθ
  rw [hcancel]
  exact MonObj.lift_comp_one_left _ _

end S_AlgebraicGeometry_GrpObj_mul_eq_of_one_eq
end P2MW
export P2MW.S_AlgebraicGeometry_GrpObj_mul_eq_of_one_eq (solution)
