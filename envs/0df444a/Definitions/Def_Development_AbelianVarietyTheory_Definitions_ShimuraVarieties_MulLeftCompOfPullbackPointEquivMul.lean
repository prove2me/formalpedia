-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MulLeftCompOfPullbackPointEquivMul
-- name    : Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MulLeftCompOfPullbackPointEquivMul
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T08:34:26.527049+00:00
-- url     : https://prove2.me/theorems/30451e46-77ac-4b0e-bdd1-69f9fb69261b
-- title:
--   Mul Left Comp Of Pullback Point Equiv Mul
-- statement:
--   Definitions and structural lemmas for Mul Left Comp Of Pullback Point Equiv Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/MulLeftCompOfPullbackPointEquivMul.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_OverHomEqIffForallIsAlgClosedAlgebra
import Theorems.Thm_GlobalTheory_AddLaw_Proportional_symm
import Theorems.Thm_GlobalTheory_ProjPoint_hom_ext
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_affineX
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_affineY
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_algebraMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affinePointEquiv_apply
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affinePointEquiv_symm_zeroOver
import Theorems.Thm_GlobalTheory_WeierstrassCurve_ofAffinePoint_some
import Theorems.Thm_GlobalTheory_WeierstrassCurve_ofAffinePoint_toAffineLift
import Theorems.Thm_GlobalTheory_WeierstrassCurve_ofAffinePoint_zero
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_algebraMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_originW
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_originZ
import Theorems.Thm_GlobalTheory_WeierstrassCurve_projectivePointEquiv_apply
import Theorems.Thm_GlobalTheory_WeierstrassCurve_projectivePointEquiv_symm_zeroOver
import Theorems.Thm_GlobalTheory_over_hom_eq_iff_forall_field_algebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_affineX
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_affineY
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_algebraMap
attribute [local simp] GlobalTheory.WeierstrassCurve.affinePointEquiv_apply
attribute [local simp] GlobalTheory.WeierstrassCurve.affinePointEquiv_symm_zeroOver
attribute [local simp] GlobalTheory.WeierstrassCurve.ofAffinePoint_some
attribute [local simp] GlobalTheory.WeierstrassCurve.ofAffinePoint_toAffineLift
attribute [local simp] GlobalTheory.WeierstrassCurve.ofAffinePoint_zero
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_algebraMap
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_originW
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_originZ
attribute [local simp] GlobalTheory.WeierstrassCurve.projectivePointEquiv_apply
attribute [local simp] GlobalTheory.WeierstrassCurve.projectivePointEquiv_symm_zeroOver


set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
universe u
noncomputable section
namespace GlobalTheory
abbrev specOver (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] : Over (Spec (.of R)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))
section Glue
variable {R : Type u} [CommRing R]
end Glue
section Pullback
variable {S S' : Scheme.{u}} {G : Over S} {G' : Over S'} {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
def pullbackPointEquiv (h : IsPullback φ G'.hom G.hom f) (T : Over S') :
    (T ⟶ G') ≃ ((Over.map f).obj T ⟶ G) where
  toFun x := Over.homMk (x.left ≫ φ) (by
    change (x.left ≫ φ) ≫ G.hom = T.hom ≫ f
    rw [Category.assoc, h.w, Over.w_assoc])
  invFun y := Over.homMk (h.lift y.left T.hom (Over.w y)) (h.lift_snd ..)
  left_inv x := Over.OverMorphism.ext (h.hom_ext (h.lift_fst ..)
    ((h.lift_snd ..).trans (Over.w x).symm))
  right_inv y := Over.OverMorphism.ext (h.lift_fst ..)
@[simp] theorem pullbackPointEquiv_apply_left (h : IsPullback φ G'.hom G.hom f) {T : Over S'}
    (x : T ⟶ G') : (pullbackPointEquiv h T x).left = x.left ≫ φ := rfl
def pullbackRepresentableBy [GrpObj G] (h : IsPullback φ G'.hom G.hom f) :
    (((Over.map f).op ⋙ yonedaGrpObj G) ⋙ forget _).RepresentableBy G' where
  homEquiv {T} := pullbackPointEquiv h T
  homEquiv_comp _ _ := Over.OverMorphism.ext (Category.assoc _ _ _)
@[instance_reducible]
def grpObjOfIsPullback [GrpObj G] (h : IsPullback φ G'.hom G.hom f) : GrpObj G' :=
  GrpObj.ofRepresentableBy G' _ (pullbackRepresentableBy h)
end Pullback
section FieldPoints
variable {R : Type u} [CommRing R] {G : Over (Spec (.of R))}
@[instance_reducible]
def grpObjOfFieldPoints [IsSeparated G.hom] [IsReduced G.left] [IsReduced ((G ⊗ G) ⊗ G).left]
    (e : 𝟙_ _ ⟶ G) (m : G ⊗ G ⟶ G) (i : G ⟶ G)
    (H : ∀ (k : Type u) [Field k] [Algebra R k], ∃ (M : Type u) (_ : AddCommGroup M)
      (c : M ≃ (specOver R k ⟶ G)), toUnit _ ≫ e = c 0 ∧
        (∀ a b, lift (c a) (c b) ≫ m = c (a + b)) ∧ ∀ a, c a ≫ i = c (-a)) : GrpObj G where
  one := e
  mul := m
  inv := i
  one_mul :=
    have : IsIso (λ_ G).hom.left := ((Over.forget _).mapIso (λ_ G)).isIso_hom
    have : IsReduced (𝟙_ _ ⊗ G).left := isReduced_of_isOpenImmersion (λ_ G).hom.left
    over_hom_eq_iff_forall_field_algebra.mpr fun k _ _ x => by
    obtain ⟨M, _, c, h₀, h₁, h₂⟩ := H k
    obtain ⟨a, ha⟩ := c.surjective (x ≫ snd _ _)
    obtain rfl : x = lift (toUnit _) (c a) :=
      CartesianMonoidalCategory.hom_ext _ _ (toUnit_unique _ _) (by simp [ha])
    simp [h₀, h₁]
  mul_one :=
    have : IsIso (ρ_ G).hom.left := ((Over.forget _).mapIso (ρ_ G)).isIso_hom
    have : IsReduced (G ⊗ 𝟙_ _).left := isReduced_of_isOpenImmersion (ρ_ G).hom.left
    over_hom_eq_iff_forall_field_algebra.mpr fun k _ _ x => by
    obtain ⟨M, _, c, h₀, h₁, h₂⟩ := H k
    obtain ⟨a, ha⟩ := c.surjective (x ≫ fst _ _)
    obtain rfl : x = lift (c a) (toUnit _) :=
      CartesianMonoidalCategory.hom_ext _ _ (by simp [ha]) (toUnit_unique _ _)
    simp [h₀, h₁]
  mul_assoc := over_hom_eq_iff_forall_field_algebra.mpr fun k _ _ x => by
    obtain ⟨M, _, c, h₀, h₁, h₂⟩ := H k
    obtain ⟨a, ha⟩ := c.surjective (x ≫ fst _ _ ≫ fst _ _)
    obtain ⟨b, hb⟩ := c.surjective (x ≫ fst _ _ ≫ snd _ _)
    obtain ⟨d, hd⟩ := c.surjective (x ≫ snd _ _)
    obtain rfl : x = lift (lift (c a) (c b)) (c d) := by ext <;> simp [ha, hb, hd]
    simp [h₁, add_assoc]
  left_inv := over_hom_eq_iff_forall_field_algebra.mpr fun k _ _ x => by
    obtain ⟨M, _, c, h₀, h₁, h₂⟩ := H k
    obtain ⟨a, rfl⟩ := c.surjective x
    simp [comp_lift_assoc, h₀, h₁, h₂]
  right_inv := over_hom_eq_iff_forall_field_algebra.mpr fun k _ _ x => by
    obtain ⟨M, _, c, h₀, h₁, h₂⟩ := H k
    obtain ⟨a, rfl⟩ := c.surjective x
    simp [comp_lift_assoc, h₀, h₁, h₂]
end FieldPoints
end GlobalTheory


