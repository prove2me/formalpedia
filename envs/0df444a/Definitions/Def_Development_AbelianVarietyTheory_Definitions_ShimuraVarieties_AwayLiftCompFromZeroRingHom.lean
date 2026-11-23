-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_AwayLiftCompFromZeroRingHom
-- name    : Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_AwayLiftCompFromZeroRingHom
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:51:56.145891+00:00
-- url     : https://prove2.me/theorems/e43c53df-58a9-44a3-b278-976ac76ffe75
-- title:
--   Away Lift Comp From Zero Ring Hom
-- statement:
--   Definitions and structural lemmas for Away Lift Comp From Zero Ring Hom, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/AwayLiftCompFromZeroRingHom.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory HomogeneousLocalization HomogeneousIdeal
universe u
noncomputable section
namespace GlobalTheory
section Quot
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (𝒜 : ℕ → Submodule R A)
def quotGrading (I : Ideal A) : ℕ → Submodule R (A ⧸ I) :=
  fun d => (𝒜 d).map (Ideal.Quotient.mkₐ R I).toLinearMap
variable [GradedAlgebra 𝒜]
theorem isInternal_quotGrading {I : Ideal A} (hI : I.IsHomogeneous 𝒜) :
    DirectSum.IsInternal (quotGrading 𝒜 I) := by
  classical
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  constructor
  · rw [iSupIndep_def]
    intro i
    rw [Submodule.disjoint_def]
    rintro y ⟨a, ha, rfl⟩ hy
    have hmap : (⨆ (j) (_ : j ≠ i), quotGrading 𝒜 I j) =
        (⨆ (j) (_ : j ≠ i), 𝒜 j).map (Ideal.Quotient.mkₐ R I).toLinearMap := by
      simp only [quotGrading, Submodule.map_iSup]
    rw [hmap] at hy
    obtain ⟨b, hb, hab⟩ := hy
    have hb0 : GradedRing.proj 𝒜 i b = 0 := by
      refine Submodule.iSup_induction _ (motive := fun x => GradedRing.proj 𝒜 i x = 0) hb ?_
        (map_zero _) (fun x y hx hy => by simp only [map_add, hx, hy, add_zero])
      intro j x hx
      refine Submodule.iSup_induction _ (motive := fun x => GradedRing.proj 𝒜 i x = 0) hx ?_
        (map_zero _) (fun x y hx hy => by simp only [map_add, hx, hy, add_zero])
      intro hji z hz
      rw [GradedRing.proj_apply, DirectSum.decompose_of_mem_ne 𝒜 hz hji]
    have hab' : a - b ∈ I := Ideal.Quotient.eq.mp hab.symm
    have h2 : GradedRing.proj 𝒜 i (a - b) ∈ I := hI i hab'
    rw [map_sub, hb0, sub_zero, GradedRing.proj_apply,
      DirectSum.decompose_of_mem_same 𝒜 ha] at h2
    exact Ideal.Quotient.eq_zero_iff_mem.mpr h2
  · have htop := (DirectSum.Decomposition.isInternal 𝒜).submodule_iSup_eq_top
    change (⨆ d, (𝒜 d).map (Ideal.Quotient.mkₐ R I).toLinearMap) = ⊤
    rw [← Submodule.map_iSup, htop, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (Ideal.Quotient.mkₐ_surjective R I)
instance gradedMonoid_quotGrading (I : Ideal A) : SetLike.GradedMonoid (quotGrading 𝒜 I) where
  one_mem := ⟨1, SetLike.GradedOne.one_mem, map_one (Ideal.Quotient.mkₐ R I)⟩
  mul_mem := by
    rintro i j _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, SetLike.GradedMul.mul_mem ha hb, map_mul (Ideal.Quotient.mkₐ R I) a b⟩
@[reducible] def quotGradedAlgebra {I : Ideal A} (hI : I.IsHomogeneous 𝒜) :
    GradedAlgebra (quotGrading 𝒜 I) where
  toGradedMonoid := inferInstance
  toDecomposition := (isInternal_quotGrading 𝒜 hI).chooseDecomposition
end Quot
namespace ProjPoint
variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {B C : Type u} [CommRing B] [CommRing C]
def awayLift (φ : A →+* B) (f : A) (hf : IsUnit (φ f)) : Away 𝒜 f →+* B :=
  (IsLocalization.Away.lift (S := Localization.Away f) f hf).comp
    (algebraMap (Away 𝒜 f) (Localization.Away f))
theorem map_irrelevant_comp {φ : A →+* B} (hφ : (irrelevant 𝒜).toIdeal.map φ = ⊤) (ψ : B →+* C) :
    (irrelevant 𝒜).toIdeal.map (ψ.comp φ) = ⊤ := by
  rw [← Ideal.map_map, hφ, Ideal.map_top]
def ofHom (φ : A →+* B) (hφ : (irrelevant 𝒜).toIdeal.map φ = ⊤) : Spec (.of B) ⟶ Proj 𝒜 :=
  Proj.fromOfGlobalSections 𝒜 ((Scheme.ΓSpecIso (.of B)).inv.hom.comp φ)
    (map_irrelevant_comp 𝒜 hφ _)
section Map
variable {A' τ τ' : Type u} {A₀ : Type u} [CommRing A₀] [CommRing A'] [SetLike τ A₀]
  [AddSubgroupClass τ A₀] [SetLike τ' A'] [AddSubgroupClass τ' A']
  {𝒜₀ : ℕ → τ} {ℬ : ℕ → τ'} [GradedRing 𝒜₀] [GradedRing ℬ]
theorem map_irrelevant_comp_graded (g : 𝒜₀ →+*ᵍ ℬ) (hg : irrelevant ℬ ≤ (irrelevant 𝒜₀).map g)
    {φ : A' →+* B} (hφ : (irrelevant ℬ).toIdeal.map φ = ⊤) :
    (irrelevant 𝒜₀).toIdeal.map (φ.comp g.toRingHom) = ⊤ := by
  rw [← Ideal.map_map, _root_.eq_top_iff, ← hφ]
  exact Ideal.map_mono hg
end Map
end ProjPoint
end GlobalTheory


