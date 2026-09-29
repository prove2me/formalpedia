-- Prove2me | solution 1 for AlgebraicGeometry.PolarisedAbelianScheme.Satisfying.exists_isFineModuli_of_isFineModuli_framed_of_finite_free_transitive_of_three_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/f860df8c-83bd-5118-871e-e4c844388cdc

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType
import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_quotient_of_finite_of_forall_exists_isAffineOpen_invariant
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_isAffineOpen_mem_forall_preimage_eq_of_forall_finset_of_isSeparated
import Theorems.Thm_AlgebraicGeometry_Scheme_finite_flat_and_locally_eq_comp_of_free_of_quotient
import Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_Satisfying_framedPt_comp_eq_of_iso_of_finite_free_transitive
import Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_Satisfying_exists_pt_comp_eq_of_finite_free_transitive
import Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_Satisfying_exists_pt_eq_of_finite_free_transitive
import Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_Satisfying_iso_of_pt_eq_of_finite_free_transitive
import Theorems.Thm_AlgebraicGeometry_Scheme_isSeparated_quasiCompact_locallyOfFinitePresentation_of_quotient_of_finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_Satisfying_exists_isFineModuli_of_isFineModuli_framed_of_finite_free_transitive_of_three_le
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

theorem solution
    (g N n : ℕ) (hn : 3 ≤ n) (𝒪 : Type) [CommRing 𝒪] (hn' : IsUnit ((n : ℕ) : 𝒪))
    (Q : ∀ (S : Type) [CommRing S], PolarisedAbelianScheme g (N + 1) n S → Prop)

    (hQbc : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (u : PolarisedAbelianScheme g (N + 1) n S) (u' : PolarisedAbelianScheme g (N + 1) n S'),
      PolarisedAbelianScheme.IsPullback φ u u' → Q S u → Q S' u')
    (hQdesc : ∀ (S S' : Type) [CommRing S] [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S'] [Algebra.Etale S S']
      (u : PolarisedAbelianScheme g (N + 1) n S) (u' : PolarisedAbelianScheme g (N + 1) n S'),
      PolarisedAbelianScheme.IsPullback (algebraMap S S') u u' → Q S' u' → Q S u)
    (hSHEAF : ∀ {g d n : ℕ} (hn : 3 ≤ n) {S : Type} [CommRing S] (hn' : IsUnit ((n : ℕ) : S))
      {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
      (B : Fin k → Type) [∀ i, CommRing (B i)] [∀ i, Algebra S (B i)] [∀ i, IsLocalization.Away (r i) (B i)],
      (∀ (u : ∀ i, PolarisedAbelianScheme g d n (B i)),
      (∀ (i j : Fin k) (C : Type) [CommRing C] [Algebra S C] [IsLocalization.Away (r i * r j) C]
      (ρ₁ : B i →ₐ[S] C) (ρ₂ : B j →ₐ[S] C) (v₁ v₂ : PolarisedAbelianScheme g d n C),
      PolarisedAbelianScheme.IsPullback ρ₁.toRingHom (u i) v₁ →
      PolarisedAbelianScheme.IsPullback ρ₂.toRingHom (u j) v₂ →
      PolarisedAbelianScheme.Iso v₁ v₂) →
      ∃ u₀ : PolarisedAbelianScheme g d n S, ∀ (i : Fin k) (v : PolarisedAbelianScheme g d n (B i)),
      PolarisedAbelianScheme.IsPullback (algebraMap S (B i)) u₀ v → PolarisedAbelianScheme.Iso v (u i)) ∧
      (∀ (u₀ u₀' : PolarisedAbelianScheme g d n S),
      (∀ (i : Fin k) (v v' : PolarisedAbelianScheme g d n (B i)),
      PolarisedAbelianScheme.IsPullback (algebraMap S (B i)) u₀ v →
      PolarisedAbelianScheme.IsPullback (algebraMap S (B i)) u₀' v' →
      PolarisedAbelianScheme.Iso v v') →
      PolarisedAbelianScheme.Iso u₀ u₀'))
    (hEFF : ∀ {g d n : ℕ} (hn : 3 ≤ n) {S : Type} [CommRing S] (hn' : IsUnit ((n : ℕ) : S))
      (S' : Type) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
      (u' : PolarisedAbelianScheme g d n S')
      (hdesc : ∀ (v₁ v₂ : PolarisedAbelianScheme g d n (S' ⊗[S] S')),
      PolarisedAbelianScheme.IsPullback
      (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S').toRingHom u' v₁ →
      PolarisedAbelianScheme.IsPullback
      (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom u' v₂ →
      PolarisedAbelianScheme.Iso v₁ v₂),
      (∃ u : PolarisedAbelianScheme g d n S, ∀ v : PolarisedAbelianScheme g d n S',
      PolarisedAbelianScheme.IsPullback (algebraMap S S') u v → PolarisedAbelianScheme.Iso v u') ∧
      (∀ (u₁ u₂ : PolarisedAbelianScheme g d n S) (v₁ v₂ : PolarisedAbelianScheme g d n S'),
      PolarisedAbelianScheme.IsPullback (algebraMap S S') u₁ v₁ →
      PolarisedAbelianScheme.IsPullback (algebraMap S S') u₂ v₂ →
      PolarisedAbelianScheme.Iso v₁ v₂ → PolarisedAbelianScheme.Iso u₁ u₂))
    (hBC : ∀ {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') (u : PolarisedAbelianScheme g (N + 1) n S),
      ∃ u' : PolarisedAbelianScheme g (N + 1) n S', PolarisedAbelianScheme.IsPullback φ u u')
    (Θ : ∀ (S : Type) [CommRing S], FramedPolarisedAbelianScheme g N n S → Prop)
    (hΘQ : ∀ (S : Type) [CommRing S] (_s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (X : FramedPolarisedAbelianScheme g N n S), Θ S X → Q S X.toPolarisedAbelianScheme)
    (hΘiso : ∀ (S : Type) [CommRing S] (X X' : FramedPolarisedAbelianScheme g N n S),
      FramedPolarisedAbelianScheme.Iso X X' → Θ S X → Θ S X')
    (hΘbc : ∀ (S S' : Type) [CommRing S] [CommRing S'] (_s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (φ : S →+* S')
      (X : FramedPolarisedAbelianScheme g N n S) (X' : FramedPolarisedAbelianScheme g N n S'),
      FramedPolarisedAbelianScheme.IsPullback φ X X' → Θ S X → Θ S' X')
    (hΘBC : ∀ {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') (X : FramedPolarisedAbelianScheme g N n S),
      ∃ X' : FramedPolarisedAbelianScheme g N n S', FramedPolarisedAbelianScheme.IsPullback φ X X')
    (HΘ : Scheme.{0}) (πΘ : HΘ ⟶ Spec (CommRingCat.of 𝒪))
    (ptΘ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (X : FramedPolarisedAbelianScheme g N n S), Θ S X → SchemeHomOver s πΘ)
    (hpt_iso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (X X' : FramedPolarisedAbelianScheme g N n S) (hX : Θ S X) (hX' : Θ S X'),
      FramedPolarisedAbelianScheme.Iso X X' → ptΘ S s X hX = ptΘ S s X' hX')
    (hpt_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of 𝒪)),
      Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
      ∀ (X : FramedPolarisedAbelianScheme g N n S) (X' : FramedPolarisedAbelianScheme g N n S') (hX : Θ S X) (hX' : Θ S' X'),
      FramedPolarisedAbelianScheme.IsPullback φ X X' →
      (ptΘ S' s' X' hX').1 = Spec.map (CommRingCat.ofHom φ) ≫ (ptΘ S s X hX).1)
    (hpt_surjective : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (x : SchemeHomOver s πΘ),
      ∃ (X : FramedPolarisedAbelianScheme g N n S) (hX : Θ S X), ptΘ S s X hX = x)
    (hpt_injective : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (X X' : FramedPolarisedAbelianScheme g N n S) (hX : Θ S X) (hX' : Θ S X'), ptΘ S s X hX = ptΘ S s X' hX' →
      FramedPolarisedAbelianScheme.Iso X X')
    (hsep : IsSeparated πΘ) (hqc : QuasiCompact πΘ) (hfp : LocallyOfFinitePresentation πΘ)
    (hAF : ∀ F : Finset HΘ, ∃ U : HΘ.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U)
    (Γ : Type) [Group Γ] [Finite Γ] (ρ : Γ →* Aut HΘ) (hρ : ∀ γ : Γ, (ρ γ).hom ≫ πΘ = πΘ)
    (act : ∀ (S : Type) [CommRing S], (Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) →
      Γ → FramedPolarisedAbelianScheme g N n S → FramedPolarisedAbelianScheme g N n S)
    (hactΘ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (γ : Γ) (X : FramedPolarisedAbelianScheme g N n S), Θ S X → Θ S (act S s γ X))
    (hact_val : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (γ : Γ) (X : FramedPolarisedAbelianScheme g N n S),
      (act S s γ X).toPolarisedAbelianScheme = X.toPolarisedAbelianScheme)
    (hact_pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (γ : Γ) (X : FramedPolarisedAbelianScheme g N n S) (hX : Θ S X),
      (ptΘ S s (act S s γ X) (hactΘ S s γ X hX)).1 = (ptΘ S s X hX).1 ≫ (ρ γ).hom)

    (hfree : ∀ (S : Type) [CommRing S] [Nontrivial S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (γ : Γ)
      (X : FramedPolarisedAbelianScheme g N n S), Θ S X → FramedPolarisedAbelianScheme.Iso (act S s γ X) X → γ = 1)

    (htrans : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (X X' : FramedPolarisedAbelianScheme g N n S), Θ S X → Θ S X' →
      PolarisedAbelianScheme.Iso X.toPolarisedAbelianScheme X'.toPolarisedAbelianScheme →
      ∃ (m : ℕ) (r : Fin m → S), Ideal.span (Set.range r) = ⊤ ∧ ∀ (j : Fin m)
        (Y Y' : FramedPolarisedAbelianScheme g N n (Localization.Away (r j))),
        FramedPolarisedAbelianScheme.IsPullback (algebraMap S (Localization.Away (r j))) X Y →
        FramedPolarisedAbelianScheme.IsPullback (algebraMap S (Localization.Away (r j))) X' Y' →
        ∃ γ : Γ, FramedPolarisedAbelianScheme.Iso
          (act (Localization.Away (r j)) (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r j)))) ≫ s) γ Y) Y')

    (hsurj : ∀ (S : Type) [CommRing S] (_s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (u : PolarisedAbelianScheme g (N + 1) n S), Q S u →
      ∃ (S' : Type) (_ : CommRing S') (_ : Algebra S S'), Module.FaithfullyFlat S S' ∧
        ∃ X' : FramedPolarisedAbelianScheme g N n S', Θ S' X' ∧
          PolarisedAbelianScheme.IsPullback (algebraMap S S') u X'.toPolarisedAbelianScheme) :
    ∃ (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of 𝒪))
      (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
        PolarisedAbelianScheme.Satisfying g (N + 1) n Q S → SchemeHomOver s πM)
      (q : HΘ ⟶ M) (hq : ∀ γ : Γ, (ρ γ).hom ≫ q = q),
      (PolarisedAbelianScheme.Satisfying.IsFineModuli g (N + 1) n Q M πM pt ∧
        IsSeparated πM ∧ QuasiCompact πM ∧ LocallyOfFinitePresentation πM ∧
        (∀ F : Finset M, ∃ U : M.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U)) ∧

      (q ≫ πM = πΘ ∧ IsFinite q ∧ Flat q ∧ Function.Surjective q.base ∧
        (∀ x x' : HΘ, q.base x = q.base x' ↔ ∃ γ : Γ, (ρ γ).hom.base x = x') ∧
        (∀ V : M.Opens, Function.Injective (q.app V)) ∧
        (∀ V : M.Opens, Set.range (q.app V) =
          {t | ∀ γ : Γ, (ρ γ).hom.appLE (q ⁻¹ᵁ V) (q ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hq γ]) t = t}) ∧
        (∀ U : HΘ.Opens, IsAffineOpen U → (∀ γ : Γ, (ρ γ).hom ⁻¹ᵁ U = U) → ∃ V : M.Opens, IsAffineOpen V ∧ q ⁻¹ᵁ V = U))  := by
  classical
  haveI : Fintype Γ := Fintype.ofFinite Γ

  have hfree_pt : ∀ (K : Type) [Field K] (x : Spec (CommRingCat.of K) ⟶ HΘ) (γ : Γ), x ≫ (ρ γ).hom = x → γ = 1 := by
    intro K _ x γ hx
    obtain ⟨X, hX, hXx⟩ := hpt_surjective K (x ≫ πΘ) ⟨x, rfl⟩
    refine hfree K (x ≫ πΘ) γ X hX (hpt_injective K (x ≫ πΘ) _ _ (hactΘ K _ γ X hX) hX ?_)
    apply Subtype.ext
    rw [hact_pt K (x ≫ πΘ) γ X hX, hXx]
    exact hx

  have hadm := AlgebraicGeometry.Scheme.exists_isAffineOpen_mem_forall_preimage_eq_of_forall_finset_of_isSeparated πΘ ρ hAF
  obtain ⟨M, q, hq, hqint, hqaff, hqsurj, hqfib, hqinj, hqrange, hqdesc, hquniv⟩ :=
    AlgebraicGeometry.Scheme.exists_quotient_of_finite_of_forall_exists_isAffineOpen_invariant ρ hadm
  obtain ⟨πM, hqπ, -⟩ := hquniv (Spec (CommRingCat.of 𝒪)) πΘ hρ

  obtain ⟨hqfin, hqflat, hqet, hqfp, hqloc, hquniq⟩ := AlgebraicGeometry.Scheme.finite_flat_and_locally_eq_comp_of_free_of_quotient ρ hadm q hq hqaff hqsurj hqfib hqinj hqrange hfree_pt

  obtain ⟨hsepM, hqcM, hfpM, hAFM⟩ := AlgebraicGeometry.Scheme.isSeparated_quasiCompact_locallyOfFinitePresentation_of_quotient_of_finite 𝒪 HΘ M πΘ πM hsep hqc hfp hAF Γ ρ hρ q hq hqπ hqfin hqflat hqfp hqsurj hqfib hqdesc hqloc

  have horbit := AlgebraicGeometry.PolarisedAbelianScheme.Satisfying.framedPt_comp_eq_of_iso_of_finite_free_transitive g N n hn 𝒪 hn' Q hQbc hQdesc hSHEAF hEFF hBC Θ hΘQ hΘiso hΘbc hΘBC HΘ πΘ ptΘ hpt_iso hpt_pullback hpt_surjective hpt_injective hsep hqc hfp hAF Γ ρ hρ act hactΘ hact_val hact_pt hfree htrans hsurj M πM q hq hqπ
  obtain ⟨pt, hchar, hpt_iso', hpt_pb'⟩ := AlgebraicGeometry.PolarisedAbelianScheme.Satisfying.exists_pt_comp_eq_of_finite_free_transitive g N n hn 𝒪 hn' Q hQbc hQdesc hSHEAF hEFF hBC Θ hΘQ hΘiso hΘbc hΘBC HΘ πΘ ptΘ hpt_iso hpt_pullback hpt_surjective hpt_injective hsep hqc hfp hAF Γ ρ hρ act hactΘ hact_val hact_pt hfree htrans hsurj M πM q hq hqπ horbit

  have hsurjM := AlgebraicGeometry.PolarisedAbelianScheme.Satisfying.exists_pt_eq_of_finite_free_transitive g N n hn 𝒪 hn' Q hQbc hQdesc hSHEAF hEFF hBC Θ hΘQ hΘiso hΘbc hΘBC HΘ πΘ ptΘ hpt_iso hpt_pullback hpt_surjective hpt_injective hsep hqc hfp hAF Γ ρ hρ act hactΘ hact_val hact_pt hfree htrans hsurj M πM q hq hqπ hqfin hqflat hqet hqsurj hqloc hquniq pt hchar
  have hinjM := AlgebraicGeometry.PolarisedAbelianScheme.Satisfying.iso_of_pt_eq_of_finite_free_transitive g N n hn 𝒪 hn' Q hQbc hQdesc hSHEAF hEFF hBC Θ hΘQ hΘiso hΘbc hΘBC HΘ πΘ ptΘ hpt_iso hpt_pullback hpt_surjective hpt_injective hsep hqc hfp hAF Γ ρ hρ act hactΘ hact_val hact_pt hfree htrans hsurj M πM q hq hqπ hqfin hqflat hqet hqsurj hqloc hquniq pt hchar
  exact ⟨M, πM, pt, q, hq, ⟨⟨hpt_iso', hpt_pb', hsurjM, hinjM⟩, hsepM, hqcM, hfpM, hAFM⟩,
    hqπ, hqfin, hqflat, hqsurj, hqfib, hqinj, hqrange, hqdesc⟩

end S_AlgebraicGeometry_PolarisedAbelianScheme_Satisfying_exists_isFineModuli_of_isFineModuli_framed_of_finite_free_transitive_of_three_le
end P2MW
export P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_Satisfying_exists_isFineModuli_of_isFineModuli_framed_of_finite_free_transitive_of_three_le (solution)
