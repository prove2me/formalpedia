-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_quotient_isPullback_of_galois_of_finite_action
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/81aa6648-bd41-580f-96e5-66be5363d01f

import Mathlib
import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_quotient_of_finite_of_forall_exists_isAffineOpen_invariant
import Theorems.Thm_AlgebraicGeometry_Scheme_forall_exists_isAffineOpen_invariant_of_isSeparated_of_finset
import Theorems.Thm_AlgebraicGeometry_Scheme_isPullback_of_quotient_of_galois_of_finite_action
import Theorems.Thm_AlgebraicGeometry_quasiCompact_and_isSeparated_of_isPullback_of_faithfullyFlat
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_isImmersion_proj_of_isIntegralHom_of_quotient_of_finite_of_isImmersion_proj
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_isAffineOpen_forall_mem_forall_preimage_eq_of_isSeparated_of_finset
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_isImmersion_proj_comp_of_isImmersion_proj_of_finite_free
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_exists_quotient_isPullback_of_galois_of_finite_action
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModulePreGlue AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.glueComponent_glueMk AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.injEq AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.sizeOf_spec AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ"

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators TensorProduct

theorem iso_appLE_congr {X : Scheme.{0}} {e₁ e₂ : X ≅ X} (h : e₁ = e₂)
    (V U : X.Opens) (p₁ : U ≤ e₁.hom ⁻¹ᵁ V) (p₂ : U ≤ e₂.hom ⁻¹ᵁ V) (t : Γ(X, V)) :
    e₁.hom.appLE V U p₁ t = e₂.hom.appLE V U p₂ t := by
  subst h; rfl

theorem solution
    (𝒪 : Type) [CommRing 𝒪] (𝒪' : Type) [CommRing 𝒪'] [Algebra 𝒪 𝒪'] [Module.Finite 𝒪 𝒪'] [Module.Free 𝒪 𝒪']
    [Module.FaithfullyFlat 𝒪 𝒪']
    (G : Type) [Group G] [Finite G] (τ : G →* (𝒪' ≃ₐ[𝒪] 𝒪'))
    (hgal : Function.Bijective fun x : 𝒪' ⊗[𝒪] 𝒪' => fun σ : G =>
      Algebra.TensorProduct.lmul' (S := 𝒪') 𝒪
        (Algebra.TensorProduct.map (AlgHom.id 𝒪 𝒪') ((τ σ : 𝒪' ≃ₐ[𝒪] 𝒪') : 𝒪' →ₐ[𝒪] 𝒪') x))
    (M' : Scheme.{0}) (πM' : M' ⟶ Spec (CommRingCat.of 𝒪'))
    (hsep : IsSeparated πM') (hqc : QuasiCompact πM') (hfp : LocallyOfFinitePresentation πM')
    (hAF : ∀ F : Finset M', ∃ U : M'.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U)
    (hQP : ∃ (qpn : ℕ) (qpι : M' ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (qpn + 1)) 𝒪')),
      IsImmersion qpι ∧ qpι ≫ ProjSpace.π 𝒪' qpn = πM')
    (ρ : G → (M' ≅ M')) (hρ1 : (ρ 1).hom = 𝟙 M') (hρmul : ∀ σ σ' : G, (ρ (σ * σ')).hom = (ρ σ).hom ≫ (ρ σ').hom)
    (hρπ : ∀ σ : G, (ρ σ).hom ≫ πM' = πM' ≫ Spec.map (CommRingCat.ofHom ((τ σ : 𝒪' ≃ₐ[𝒪] 𝒪') : 𝒪' →+* 𝒪'))) :
    ∃ (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of 𝒪)) (q : M' ⟶ M),
      (∀ σ : G, (ρ σ).hom ≫ q = q) ∧
      CategoryTheory.IsPullback q πM' πM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 𝒪'))) ∧
      IsSeparated πM ∧ QuasiCompact πM ∧ LocallyOfFinitePresentation πM ∧
      (∀ F : Finset M, ∃ U : M.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U) ∧
      (∃ (qpn : ℕ) (qpι : M ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (qpn + 1)) 𝒪)),
        IsImmersion qpι ∧ qpι ≫ ProjSpace.π 𝒪 qpn = πM)  := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  let s : Spec (CommRingCat.of 𝒪') ⟶ Spec (CommRingCat.of 𝒪) := Spec.map (CommRingCat.ofHom (algebraMap 𝒪 𝒪'))

  let ρ' : G →* Aut M' :=
    { toFun := fun σ => ρ σ⁻¹
      map_one' := by ext; simp only [inv_one, hρ1]; rfl
      map_mul' := fun a b => by
        ext
        change (ρ (a * b)⁻¹).hom = ((ρ b⁻¹) ≪≫ (ρ a⁻¹)).hom
        rw [mul_inv_rev, hρmul, Iso.trans_hom] }
  have hρ' : ∀ σ : G, (ρ' σ).hom = (ρ σ⁻¹).hom := fun σ => rfl

  have hτs : ∀ σ : G, Spec.map (CommRingCat.ofHom ((τ σ : 𝒪' ≃ₐ[𝒪] 𝒪') : 𝒪' →+* 𝒪')) ≫ s = s := by
    intro σ
    simp only [s, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun x => (τ σ).commutes x

  have hadm := AlgebraicGeometry.Scheme.forall_exists_isAffineOpen_invariant_of_isSeparated_of_finset πM' hsep hAF ρ'
  obtain ⟨M, q, hqinv, hint, haff, hsurj, horb, hinj, hrange, hdesc, huniv⟩ :=
    AlgebraicGeometry.Scheme.exists_quotient_of_finite_of_forall_exists_isAffineOpen_invariant ρ' hadm
  have hq : ∀ σ : G, (ρ σ).hom ≫ q = q := fun σ => by
    have := hqinv σ⁻¹; rwa [hρ', inv_inv] at this

  have hinvπ : ∀ g : G, (ρ' g).hom ≫ (πM' ≫ s) = πM' ≫ s := fun g => by
    rw [hρ', ← Category.assoc, hρπ, Category.assoc, hτs]
  obtain ⟨πM, hqπ, -⟩ := huniv (Spec (CommRingCat.of 𝒪)) (πM' ≫ s) hinvπ

  have hrange' : ∀ V : M.Opens, Set.range (q.app V) =
      {t | ∀ σ : G, (ρ σ).hom.appLE (q ⁻¹ᵁ V) (q ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hq σ]) t = t} := by
    intro V
    rw [hrange V]
    ext t
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h σ
      have e : (ρ' σ⁻¹ : M' ≅ M') = ρ σ := by change ρ (σ⁻¹)⁻¹ = ρ σ; rw [inv_inv]
      exact (iso_appLE_congr e.symm _ _ _ _ t).trans (h σ⁻¹)
    · intro h g
      have e : (ρ' g : M' ≅ M') = ρ g⁻¹ := rfl
      exact (iso_appLE_congr e _ _ _ _ t).trans (h g⁻¹)

  have hcart : CategoryTheory.IsPullback q πM' πM s :=
    AlgebraicGeometry.Scheme.isPullback_of_quotient_of_galois_of_finite_action 𝒪 𝒪' G τ hgal M' πM' ρ hρ1 hρmul hρπ
      M πM q hq hqπ haff hinj hrange'

  haveI : QuasiCompact πM' := hqc
  haveI : IsSeparated πM' := hsep
  obtain ⟨hqcM, hsepM⟩ := AlgebraicGeometry.quasiCompact_and_isSeparated_of_isPullback_of_faithfullyFlat 𝒪' πM πM' q hcart

  have hfpM : LocallyOfFinitePresentation πM := by
    have hs : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme) s := by
      have hff : (CommRingCat.ofHom (algebraMap 𝒪 𝒪')).hom.FaithfullyFlat := by
        rw [CommRingCat.hom_ofHom, RingHom.faithfullyFlat_algebraMap_iff]; infer_instance
      obtain ⟨hfl, hsu⟩ := (AlgebraicGeometry.flat_and_surjective_SpecMap_iff _).2 hff
      exact ⟨⟨hsu, hfl⟩, inferInstance⟩
    exact MorphismProperty.of_isPullback_of_descendsAlong (P := @LocallyOfFinitePresentation)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hcart.flip hs hfp

  have hAFM : ∀ F : Finset M, ∃ U : M.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U := by
    intro F
    choose lift hlift using fun x : M => hsurj x
    obtain ⟨U, hU, hFU, hUinv⟩ := AlgebraicGeometry.Scheme.exists_isAffineOpen_forall_mem_forall_preimage_eq_of_isSeparated_of_finset πM' hsep hAF ρ' (F.image lift)
    obtain ⟨V, hV, hVU⟩ := hdesc U hU hUinv
    refine ⟨V, hV, fun x hx => ?_⟩
    have h1 : lift x ∈ q ⁻¹ᵁ V := by rw [hVU]; exact hFU _ (Finset.mem_image_of_mem lift hx)
    simpa [hlift x] using h1

  have hQP𝒪 := AlgebraicGeometry.Scheme.exists_isImmersion_proj_comp_of_isImmersion_proj_of_finite_free 𝒪 𝒪' M' πM' hQP
  have hQPM := AlgebraicGeometry.Scheme.exists_isImmersion_proj_of_isIntegralHom_of_quotient_of_finite_of_isImmersion_proj
    𝒪 M' M (πM' ≫ s) πM hQP𝒪 G ρ' hinvπ q hqinv hqπ hint haff hsurj horb hinj hrange hdesc hsepM hqcM hfpM
  exact ⟨M, πM, q, hq, hcart, hsepM, hqcM, hfpM, hAFM, hQPM⟩

end S_AlgebraicGeometry_Scheme_exists_quotient_isPullback_of_galois_of_finite_action
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_exists_quotient_isPullback_of_galois_of_finite_action (solution)
