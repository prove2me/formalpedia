-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_pointDerivations_d_zero_eq_of_d_one_eq_zero_of_isAffine_of_basicOpen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/f251a027-292d-58cc-a553-30931e2ca95d

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_Algebra_PointDerivations
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_mem_range_d_zero_of_d_one_eq_zero_of_isAffine_of_basicOpen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_pointDerivations_d_zero_eq_of_d_one_eq_zero_of_isAffine_of_basicOpen
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w

namespace PoleP2

theorem exists_linear_section {k : Type*} [Field k] {M N : Type*} [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N] (f : M →ₗ[k] N) :
    ∃ σ : N →ₗ[k] M, ∀ z ∈ LinearMap.range f, f (σ z) = z := by
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective f.rangeRestrict f.range_rangeRestrict
  obtain ⟨σ, hσ⟩ := LinearMap.exists_extend g
  refine ⟨σ, fun z hz => ?_⟩
  have h1 : σ z = g ⟨z, hz⟩ := by
    rw [← hσ]; rfl
  have h2 := congrArg Subtype.val (LinearMap.congr_fun hg ⟨z, hz⟩)
  rw [h1]
  exact h2

end PoleP2

theorem solution
    {k : Type u} [Field k] {X : Scheme.{u}} [IsAffine X] (π : X ⟶ Spec (CommRingCat.of k))
    (𝒱 : X.OrderedAffineCover) (s : 𝒱.ι → Γ(X, ⊤)) (hs : ∀ v : 𝒱.ι, 𝒱.U v = X.basicOpen (s v))
    {A : Type v} [CommRing A] [Algebra k A] (ev : A →+* k)
    {W : Type w} [AddCommGroup W] [Module k W]
    (c : ↥(Algebra.PointDerivations k A ev (W →ₗ[k] (OModulePresheaf.unit π).cochain 𝒱 1)))
    (hc : ∀ (a : A) (ξ : W), (OModulePresheaf.unit π).d 𝒱 1 (c.1 a ξ) = 0) :
    ∃ b : ↥(Algebra.PointDerivations k A ev (W →ₗ[k] (OModulePresheaf.unit π).cochain 𝒱 0)),
      ∀ (a : A) (ξ : W), (OModulePresheaf.unit π).d 𝒱 0 (b.1 a ξ) = c.1 a ξ := by
  obtain ⟨σ, hσ⟩ := PoleP2.exists_linear_section ((OModulePresheaf.unit π).d 𝒱 0 :
    (OModulePresheaf.unit π).cochain 𝒱 0 →ₗ[k] (OModulePresheaf.unit π).cochain 𝒱 1)
  let post : (W →ₗ[k] (OModulePresheaf.unit π).cochain 𝒱 1) →ₗ[k] (W →ₗ[k] (OModulePresheaf.unit π).cochain 𝒱 0) :=
    { toFun := fun F => σ.comp F
      map_add' := fun F G => by ext ξ; simp
      map_smul' := fun r F => by ext ξ; simp }
  have hpost : ∀ (F : W →ₗ[k] (OModulePresheaf.unit π).cochain 𝒱 1) (ξ : W), post F ξ = σ (F ξ) :=
    fun _ _ => rfl
  refine ⟨Algebra.PointDerivations.map ev post c, fun a ξ => ?_⟩
  have hmem := AlgebraicGeometry.OModulePresheaf.mem_range_d_zero_of_d_one_eq_zero_of_isAffine_of_basicOpen
    π 𝒱 s hs (c.1 a ξ) (hc a ξ)
  rw [Algebra.PointDerivations.map_apply_coe, hpost]
  exact hσ _ hmem

end S_AlgebraicGeometry_OModulePresheaf_exists_pointDerivations_d_zero_eq_of_d_one_eq_zero_of_isAffine_of_basicOpen
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_pointDerivations_d_zero_eq_of_d_one_eq_zero_of_isAffine_of_basicOpen (solution)
