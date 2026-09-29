-- Prove2me | solution 1 for AlgebraicGeometry.exists_isMonHom_comp_eq_of_forall_comp_eq_one_of_flat_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/ff85ae27-aac8-5c45-bd98-4a19dae1c645

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_isMonHom_comp_eq_of_forall_comp_eq_one_of_flat_of_surjective

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory"
open scoped CategoryTheory.MonObj

universe u

namespace P2mIsogFactorDesc

variable {S : Scheme.{u}} {A B C : Over S} [GrpObj A] [GrpObj B] [GrpObj C]

theorem comp_eq_comp_of_comp_eq_comp (f : A ⟶ B) [IsMonHom f] (g : A ⟶ C) [IsMonHom g]
    (hker : ∀ (T : Over S) (a : T ⟶ A), a ≫ f = 1 → a ≫ g = 1)
    {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ A.left) (h : g₁ ≫ f.left = g₂ ≫ f.left) :
    g₁ ≫ g.left = g₂ ≫ g.left := by
  have hw : g₂ ≫ A.hom = g₁ ≫ A.hom := by
    rw [← Over.w f, reassoc_of% h]
  let T : Over S := Over.mk (g₁ ≫ A.hom)
  let a₁ : T ⟶ A := Over.homMk g₁ rfl
  let a₂ : T ⟶ A := Over.homMk g₂ hw
  have hf : a₁ ≫ f = a₂ ≫ f := Over.OverMorphism.ext (by simpa [a₁, a₂] using h)
  have h1 : (a₁⁻¹ * a₂) ≫ f = 1 := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, hf, inv_mul_cancel]
  have h2 := hker T _ h1
  rw [MonObj.mul_comp, GrpObj.inv_comp, inv_mul_eq_one] at h2
  have := congrArg CommaMorphism.left h2
  simpa [a₁, a₂] using this

noncomputable def descLeft (f : A ⟶ B) [IsMonHom f] (g : A ⟶ C) [IsMonHom g]
    [Flat f.left] [Surjective f.left] [QuasiCompact f.left]
    (hker : ∀ (T : Over S) (a : T ⟶ A), a ≫ f = 1 → a ≫ g = 1) : B.left ⟶ C.left :=
  EffectiveEpi.desc f.left g.left (fun g₁ g₂ h => comp_eq_comp_of_comp_eq_comp f g hker g₁ g₂ h)

theorem fac_left (f : A ⟶ B) [IsMonHom f] (g : A ⟶ C) [IsMonHom g]
    [Flat f.left] [Surjective f.left] [QuasiCompact f.left]
    (hker : ∀ (T : Over S) (a : T ⟶ A), a ≫ f = 1 → a ≫ g = 1) :
    f.left ≫ descLeft f g hker = g.left :=
  EffectiveEpi.fac _ _ _

private noncomputable def _root_.P2mIsogFactorDesc.desc (f : A ⟶ B) [IsMonHom f] (g : A ⟶ C) [IsMonHom g]
    [Flat f.left] [Surjective f.left] [QuasiCompact f.left]
    (hker : ∀ (T : Over S) (a : T ⟶ A), a ≫ f = 1 → a ≫ g = 1) : B ⟶ C :=
  Over.homMk (descLeft f g hker) (by
    have : Epi f.left := inferInstance
    rw [← cancel_epi f.left, reassoc_of% (fac_left f g hker), Over.w f, Over.w g])

p2m_export "P2mIsogFactorDesc" "desc"
private theorem _root_.P2mIsogFactorDesc.fac (f : A ⟶ B) [IsMonHom f] (g : A ⟶ C) [IsMonHom g]
    [Flat f.left] [Surjective f.left] [QuasiCompact f.left]
    (hker : ∀ (T : Over S) (a : T ⟶ A), a ≫ f = 1 → a ≫ g = 1) :
    f ≫ desc f g hker = g :=
  Over.OverMorphism.ext (by simp [desc, fac_left])

p2m_export "P2mIsogFactorDesc" "fac"
omit [GrpObj A] [GrpObj B] in

theorem epi_over (f : A ⟶ B) [Flat f.left] [Surjective f.left] [QuasiCompact f.left] : Epi f :=
  (Over.forget S).epi_of_epi_map (inferInstance : Epi f.left)

theorem uniq (f : A ⟶ B) [IsMonHom f] (g : A ⟶ C) [IsMonHom g]
    [Flat f.left] [Surjective f.left] [QuasiCompact f.left]
    (hker : ∀ (T : Over S) (a : T ⟶ A), a ≫ f = 1 → a ≫ g = 1)
    (h' : B ⟶ C) (hh' : f ≫ h' = g) : h' = desc f g hker := by
  have := epi_over (A := A) (B := B) f
  rw [← cancel_epi f, hh', fac]

omit [GrpObj A] [GrpObj B] in

theorem epi_tensorHom (f : A ⟶ B) [Flat f.left] [Surjective f.left] [QuasiCompact f.left] :
    Epi (f ⊗ₘ f) := by
  have hP : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) (f ⊗ₘ f).left := by
    rw [Over.tensorHom_left]
    exact MorphismProperty.pullbackMap (P := (@Surjective ⊓ @Flat ⊓ @QuasiCompact))
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
      (Over.w f).symm (Over.w f).symm
  obtain ⟨⟨h1, h2⟩, h3⟩ := hP
  have : Epi (f ⊗ₘ f).left := by
    have : Surjective (f ⊗ₘ f).left := h1
    have : Flat (f ⊗ₘ f).left := h2
    have : QuasiCompact (f ⊗ₘ f).left := h3
    infer_instance
  exact (Over.forget S).epi_of_epi_map this

theorem isMonHom_desc (f : A ⟶ B) [IsMonHom f] (g : A ⟶ C) [IsMonHom g]
    [Flat f.left] [Surjective f.left] [QuasiCompact f.left]
    (hker : ∀ (T : Over S) (a : T ⟶ A), a ≫ f = 1 → a ≫ g = 1) :
    IsMonHom (desc f g hker) where
  one_hom := by
    rw [← IsMonHom.one_hom (f := f), Category.assoc, fac, IsMonHom.one_hom (f := g)]
  mul_hom := by
    have := epi_tensorHom (A := A) (B := B) f
    rw [← cancel_epi (f ⊗ₘ f), ← Category.assoc, ← IsMonHom.mul_hom (f := f), Category.assoc, fac,
      IsMonHom.mul_hom (f := g), MonoidalCategory.tensorHom_comp_tensorHom_assoc, fac]

theorem main (f : A ⟶ B) [IsMonHom f] (g : A ⟶ C) [IsMonHom g]
    [Flat f.left] [Surjective f.left] [QuasiCompact f.left]
    (hker : ∀ (T : Over S) (a : T ⟶ A), a ≫ f = 1 → a ≫ g = 1) :
    ∃ h : B ⟶ C, IsMonHom h ∧ f ≫ h = g ∧ ∀ h' : B ⟶ C, f ≫ h' = g → h' = h :=
  ⟨desc f g hker, isMonHom_desc f g hker, fac f g hker, uniq f g hker⟩

end P2mIsogFactorDesc

open P2mIsogFactorDesc in
theorem solution
    {S : Scheme.{u}} {A B C : Over S} [GrpObj A] [GrpObj B] [GrpObj C]
    (f : A ⟶ B) [IsMonHom f] (g : A ⟶ C) [IsMonHom g]
    [Flat f.left] [Surjective f.left] [QuasiCompact f.left]
    (hker : ∀ (T : Over S) (a : T ⟶ A), a ≫ f = 1 → a ≫ g = 1) :
    ∃ h : B ⟶ C, IsMonHom h ∧ f ≫ h = g ∧ ∀ h' : B ⟶ C, f ≫ h' = g → h' = h :=
  main f g hker

end S_AlgebraicGeometry_exists_isMonHom_comp_eq_of_forall_comp_eq_one_of_flat_of_surjective
end P2MW
export P2MW.S_AlgebraicGeometry_exists_isMonHom_comp_eq_of_forall_comp_eq_one_of_flat_of_surjective (solution)
