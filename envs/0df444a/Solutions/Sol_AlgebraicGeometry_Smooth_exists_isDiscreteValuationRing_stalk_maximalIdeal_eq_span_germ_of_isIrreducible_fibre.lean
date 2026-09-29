-- Prove2me | solution 1 for AlgebraicGeometry.Smooth.exists_isDiscreteValuationRing_stalk_maximalIdeal_eq_span_germ_of_isIrreducible_fibre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/53fb06bd-38f1-59a8-930d-eac1578e3541

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Smooth_algebraMap_stalk_ne_zero_and_isPrime_span_of_apply_eq_closedPoint
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_specializes_isLocalization_atPrime_stalk
import Theorems.Thm_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Smooth_exists_isDiscreteValuationRing_stalk_maximalIdeal_eq_span_germ_of_isIrreducible_fibre
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

theorem solution
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (ϖ : R) (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) [Smooth f]
    (hirr : IsIrreducible (f.base ⁻¹' {IsLocalRing.closedPoint R})) :
    ∃ ξ : X, f.base ξ = IsLocalRing.closedPoint R ∧
      (∀ Z ∈ irreducibleComponents {x : X // f.base x = IsLocalRing.closedPoint R}, ∃ z ∈ Z, z.1 = ξ) ∧
      ∃ _ : IsDomain (X.presheaf.stalk ξ), IsDiscreteValuationRing (X.presheaf.stalk ξ) ∧
        IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) =
          Ideal.span {X.presheaf.Γgerm ξ (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ϖ))} := by
  classical

  have hSc : IsClosed (f.base ⁻¹' {IsLocalRing.closedPoint R}) :=
    (IsLocalRing.isClosed_singleton_closedPoint R).preimage f.base.hom.continuous
  have hgen : IsGenericPoint hirr.genericPoint (f.base ⁻¹' {IsLocalRing.closedPoint R}) :=
    hirr.isGenericPoint_genericPoint hSc
  obtain ⟨ξ, rfl⟩ : ∃ ξ : X, ξ = hirr.genericPoint := ⟨_, rfl⟩
  have hξ : f.base hirr.genericPoint = IsLocalRing.closedPoint R := by
    have h__af := hgen.mem
    simp at h__af
    exact h__af
  have hspec : ∀ x : X, f.base x = IsLocalRing.closedPoint R → hirr.genericPoint ⤳ x :=
    fun x hx => hgen.specializes (by simp at hx; exact hx)
  refine ⟨hirr.genericPoint, hξ, ?_, ?_⟩
  ·
    intro Z hZ
    have hcl : closure ({⟨hirr.genericPoint, hξ⟩} : Set {x : X // f.base x = IsLocalRing.closedPoint R}) = Set.univ := by
      apply Set.eq_univ_of_forall
      intro z
      rw [closure_subtype, Set.image_singleton, ← specializes_iff_mem_closure]
      exact hspec z.1 z.2
    have hirr' : IsIrreducible (closure ({⟨hirr.genericPoint, hξ⟩} : Set {x : X // f.base x = IsLocalRing.closedPoint R})) :=
      isIrreducible_singleton.closure
    have hle : Z ⊆ closure {⟨hirr.genericPoint, hξ⟩} := by rw [hcl]; exact Set.subset_univ _
    have hZle := hZ.2 hirr' hle
    exact ⟨⟨hirr.genericPoint, hξ⟩, hZle (subset_closure (Set.mem_singleton _)), rfl⟩
  ·
    set ξ := hirr.genericPoint with hξdef
    letI alg : Algebra R (X.presheaf.stalk ξ) :=
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ ξ trivial).hom.toAlgebra
    have halg : X.fromSpecStalk ξ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (X.presheaf.stalk ξ))) := by
      calc X.fromSpecStalk ξ ≫ f
          = X.fromSpecStalk ξ ≫ (f ≫ (Spec (CommRingCat.of R)).toSpecΓ) ≫ (Spec (CommRingCat.of R)).isoSpec.inv := by
            rw [Category.assoc, Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]
        _ = (X.fromSpecStalk ξ ≫ X.toSpecΓ) ≫ Spec.map f.appTop ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv := by
            rw [Scheme.toSpecΓ_naturality, Scheme.isoSpec_Spec_inv, Category.assoc, Category.assoc]
        _ = Spec.map (X.presheaf.germ ⊤ ξ trivial) ≫ Spec.map f.appTop ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv := by
            rw [Scheme.fromSpecStalk_toSpecΓ]
        _ = Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ ξ trivial) := by
            rw [Spec.map_comp, Spec.map_comp, Category.assoc]
        _ = Spec.map (CommRingCat.ofHom (algebraMap R (X.presheaf.stalk ξ))) := rfl
    obtain ⟨hne, hprime⟩ :=
      AlgebraicGeometry.Smooth.algebraMap_stalk_ne_zero_and_isPrime_span_of_apply_eq_closedPoint ϖ hϖ f ξ hξ halg
    set tξ : X.presheaf.stalk ξ := algebraMap R (X.presheaf.stalk ξ) ϖ with htξ
    have hdom : IsDomain (X.presheaf.stalk ξ) :=
      (AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing R f ξ).1
    haveI := hdom
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f

    have hgerm : ∀ (x : X) (hx : x ⤳ ξ), (X.presheaf.stalkSpecializes hx) tξ =
        (X.presheaf.germ ⊤ x trivial) (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ϖ)) := by
      intro x hx
      show (X.presheaf.germ ⊤ ξ trivial ≫ X.presheaf.stalkSpecializes hx)
          (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ϖ)) = _
      rw [TopCat.Presheaf.germ_stalkSpecializes]

    have hfib : ∀ x : X, ¬ IsUnit ((X.presheaf.germ ⊤ x trivial) (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ϖ))) →
        f.base x = IsLocalRing.closedPoint R := by
      intro x hx
      by_contra hne'
      apply hx
      rw [← Scheme.mem_basicOpen]
      have hU : X.basicOpen (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ϖ)) =
          f ⁻¹ᵁ ((Spec (CommRingCat.of R)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ϖ)) :=
        (Scheme.preimage_basicOpen f _).symm
      have hb : (Spec (CommRingCat.of R)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ϖ) =
          PrimeSpectrum.basicOpen (R := (CommRingCat.of R)) ϖ := basicOpen_eq_of_affine (R := CommRingCat.of R) ϖ
      have hbset : ((f ⁻¹ᵁ ((Spec (CommRingCat.of R)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ϖ)) : X.Opens) :
          Set X) = f.base ⁻¹' {p | ϖ ∉ p.asIdeal} := by
        rw [hb]; rfl
      rw [hU, ← SetLike.mem_coe, hbset, Set.mem_preimage, Set.mem_setOf_eq]
      intro hmemϖ
      apply hne'
      apply PrimeSpectrum.ext
      show (f.base x).asIdeal = IsLocalRing.maximalIdeal R
      have hle : IsLocalRing.maximalIdeal R ≤ (f.base x).asIdeal := by
        rw [hϖ, Ideal.span_singleton_le_iff_mem]; exact hmemϖ
      exact ((IsLocalRing.maximalIdeal.isMaximal R).eq_of_le (f.base x).isPrime.ne_top hle).symm

    have hmax : IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) = Ideal.span {tξ} := by
      haveI := hprime
      obtain ⟨x, hx, hloc⟩ := AlgebraicGeometry.Scheme.exists_specializes_isLocalization_atPrime_stalk ξ (Ideal.span {tξ})
      letI algx := (X.presheaf.stalkSpecializes hx).hom.toAlgebra
      haveI := hloc
      have hnu : ¬ IsUnit ((X.presheaf.stalkSpecializes hx) tξ) := by
        intro hu
        have h1 := (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk x) (Ideal.span {tξ}) tξ).mp hu
        exact h1 (Ideal.subset_span (Set.mem_singleton tξ))
      have hfx : f.base x = IsLocalRing.closedPoint R := hfib x (by rw [← hgerm x hx]; exact hnu)
      have hxξ : x = ξ := (hx.antisymm (hspec x hfx)).eq
      subst hxξ
      have hid : X.presheaf.stalkSpecializes hx = 𝟙 _ := TopCat.Presheaf.stalkSpecializes_refl _ _
      apply le_antisymm
      · intro s hs
        by_contra hns
        have hu : IsUnit ((algebraMap (X.presheaf.stalk hirr.genericPoint) (X.presheaf.stalk hirr.genericPoint)) s) :=
          (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk hirr.genericPoint) (Ideal.span {tξ}) s).mpr hns
        have hu' : IsUnit s := by
          have : (algebraMap (X.presheaf.stalk hirr.genericPoint) (X.presheaf.stalk hirr.genericPoint)) s = s := by
            show (X.presheaf.stalkSpecializes hx) s = s
            rw [hid]; rfl
          rwa [this] at hu
        exact (IsLocalRing.mem_maximalIdeal _).mp hs hu'
      · exact IsLocalRing.le_maximalIdeal hprime.ne_top

    have hnf : ¬ IsField (X.presheaf.stalk ξ) := by
      intro hF
      apply hne
      have h0 := IsLocalRing.isField_iff_maximalIdeal_eq.mp hF
      have : tξ ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) := by
        rw [hmax]; exact Ideal.subset_span (Set.mem_singleton tξ)
      rw [h0] at this
      simpa using this
    have hprinc : (IsLocalRing.maximalIdeal (X.presheaf.stalk ξ)).IsPrincipal := ⟨⟨tξ, by rw [hmax]⟩⟩
    have hdvr : IsDiscreteValuationRing (X.presheaf.stalk ξ) :=
      ((IsDiscreteValuationRing.TFAE (X.presheaf.stalk ξ) hnf).out 0 4).mpr hprinc
    exact ⟨hdom, hdvr, hmax⟩

end S_AlgebraicGeometry_Smooth_exists_isDiscreteValuationRing_stalk_maximalIdeal_eq_span_germ_of_isIrreducible_fibre
end P2MW
export P2MW.S_AlgebraicGeometry_Smooth_exists_isDiscreteValuationRing_stalk_maximalIdeal_eq_span_germ_of_isIrreducible_fibre (solution)
