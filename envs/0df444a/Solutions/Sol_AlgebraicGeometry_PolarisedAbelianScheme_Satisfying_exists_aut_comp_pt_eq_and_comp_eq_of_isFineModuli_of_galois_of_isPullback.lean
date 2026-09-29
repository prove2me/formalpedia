-- Prove2me | solution 1 for AlgebraicGeometry.PolarisedAbelianScheme.Satisfying.exists_aut_comp_pt_eq_and_comp_eq_of_isFineModuli_of_galois_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/4b8f0a82-9f82-5b7f-ae05-1f50e5fa8690

import Mathlib
import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Theorems.Thm_AlgebraicGeometry_Scheme_existsUnique_hom_spec_comp_eq_of_natural
import Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_isPullback_univ
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_Satisfying_exists_aut_comp_pt_eq_and_comp_eq_of_isFineModuli_of_galois_of_isPullback
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators TensorProduct

namespace D2GaloisActionAux

variable {g d n : ℕ} {Q : ∀ (S : Type) [CommRing S], PolarisedAbelianScheme g d n S → Prop}
  {B : Type} [CommRing B] {M' : Scheme.{0}} {πM' : M' ⟶ Spec (CommRingCat.of B)}
  {pt' : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      PolarisedAbelianScheme.Satisfying g d n Q S → SchemeHomOver s πM'}

theorem pt_congr {S : Type} [CommRing S] {s₀ s₁ : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)} (e : s₀ = s₁)
    (X : PolarisedAbelianScheme.Satisfying g d n Q S) : (pt' S s₀ X).1 = (pt' S s₁ X).1 := by
  subst e; rfl

theorem exists_isPullback
    (hQbc : ∀ {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
      (u : PolarisedAbelianScheme g d n S) (u' : PolarisedAbelianScheme g d n S'),
      PolarisedAbelianScheme.IsPullback φ u u' → Q S u → Q S' u')
    {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') (X : PolarisedAbelianScheme.Satisfying g d n Q S) :
    ∃ X' : PolarisedAbelianScheme.Satisfying g d n Q S', PolarisedAbelianScheme.Satisfying.IsPullback φ X X' := by
  obtain ⟨u', hu'⟩ := AlgebraicGeometry.PolarisedAbelianScheme.exists_isPullback_univ φ X.val
  exact ⟨⟨u', hQbc φ X.val u' hu' X.prop⟩, hu'⟩

theorem pt_eq_of_pt_eq (hM' : PolarisedAbelianScheme.Satisfying.IsFineModuli g d n Q M' πM' pt')
    {S : Type} [CommRing S] {s₀ s₁ s₂ s₃ : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)}
    (X₀ X₁ : PolarisedAbelianScheme.Satisfying g d n Q S) (e : s₀ = s₁)
    (h : (pt' S s₀ X₀).1 = (pt' S s₁ X₁).1) (e' : s₂ = s₃) :
    (pt' S s₂ X₀).1 = (pt' S s₃ X₁).1 := by
  subst e e'
  have hiso : PolarisedAbelianScheme.Satisfying.Iso X₀ X₁ := hM'.pt_injective S s₀ X₀ X₁ (Subtype.ext h)
  rw [hM'.pt_iso S s₂ X₀ X₁ hiso]

theorem comp_pt_eq (hM' : PolarisedAbelianScheme.Satisfying.IsFineModuli g d n Q M' πM' pt')
    (hQbc : ∀ {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
      (u : PolarisedAbelianScheme g d n S) (u' : PolarisedAbelianScheme g d n S'),
      PolarisedAbelianScheme.IsPullback φ u u' → Q S u → Q S' u')
    {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (s s₂ : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
    (s' s₂' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of B))
    (hs' : Spec.map (CommRingCat.ofHom φ) ≫ s = s') (hs₂' : Spec.map (CommRingCat.ofHom φ) ≫ s₂ = s₂')
    (X : PolarisedAbelianScheme.Satisfying g d n Q S) (X' : PolarisedAbelianScheme.Satisfying g d n Q S')
    (h : (pt' S' s' X').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt' S s X).1) :
    (pt' S' s₂' X').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt' S s₂ X).1 := by
  obtain ⟨X'', hX''⟩ := exists_isPullback hQbc φ X
  have h1 := hM'.pt_pullback S S' φ s s' hs' X X'' hX''
  have hiso : PolarisedAbelianScheme.Satisfying.Iso X' X'' :=
    hM'.pt_injective S' s' X' X'' (Subtype.ext (h.trans h1.symm))
  rw [hM'.pt_iso S' s₂' X' X'' hiso]
  exact hM'.pt_pullback S S' φ s₂ s₂' hs₂' X X'' hX''

theorem exists_twist (hM' : PolarisedAbelianScheme.Satisfying.IsFineModuli g d n Q M' πM' pt')
    (hQbc : ∀ {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
      (u : PolarisedAbelianScheme g d n S) (u' : PolarisedAbelianScheme g d n S'),
      PolarisedAbelianScheme.IsPullback φ u u' → Q S u → Q S' u')
    (t : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of B)) :
    ∃ u : M' ⟶ M', u ≫ πM' = πM' ≫ t ∧
      (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
        (X : PolarisedAbelianScheme.Satisfying g d n Q S), (pt' S s X).1 ≫ u = (pt' S (s ≫ t) X).1) ∧
      ∀ v : M' ⟶ M',
        (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
          (X : PolarisedAbelianScheme.Satisfying g d n Q S), (pt' S s X).1 ≫ v = (pt' S (s ≫ t) X).1) → v = u := by
  classical
  have hrep0 : ∀ (C : Type) [CommRing C] (z : Spec (CommRingCat.of C) ⟶ M'),
      ∃ X : PolarisedAbelianScheme.Satisfying g d n Q C, (pt' C (z ≫ πM') X).1 = z := by
    intro C _ z
    obtain ⟨X, hX⟩ := hM'.pt_surjective C (z ≫ πM') ⟨z, rfl⟩
    exact ⟨X, by rw [hX]⟩
  choose rep hrep using hrep0
  obtain ⟨u, hu_over, hu_pt, hu_uniq⟩ :=
    AlgebraicGeometry.Scheme.existsUnique_hom_spec_comp_eq_of_natural (R := B) (πM' ≫ t) πM'
      (fun C _ _ z _ => (pt' C ((z ≫ πM') ≫ t) (rep C z)).1)
      (fun C _ _ z hz => by
        rw [(pt' C ((z ≫ πM') ≫ t) (rep C z)).2, Category.assoc]
        exact hz)
      (fun C C' _ _ _ _ φ z hz hz' =>
        comp_pt_eq hM' hQbc φ.toRingHom (z ≫ πM') ((z ≫ πM') ≫ t)
          ((Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ z) ≫ πM')
          (((Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ z) ≫ πM') ≫ t)
          (by simp only [Category.assoc]) (by simp only [Category.assoc])
          (rep C z) (rep C' (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ z))
          (by rw [hrep, hrep]))
  refine ⟨u, hu_over, ?_, ?_⟩
  · intro S _ s X
    letI : Algebra B S := (Spec.preimage (s ≫ t)).hom.toAlgebra
    have halg : Spec.map (CommRingCat.ofHom (algebraMap B S)) = s ≫ t := by
      show Spec.map (CommRingCat.ofHom (Spec.preimage (s ≫ t)).hom) = s ≫ t
      rw [CommRingCat.ofHom_hom, Spec.map_preimage]
    have hz : (pt' S s X).1 ≫ (πM' ≫ t) = Spec.map (CommRingCat.ofHom (algebraMap B S)) := by
      rw [halg, ← Category.assoc, (pt' S s X).2]
    rw [hu_pt S (pt' S s X).1 hz]
    exact pt_eq_of_pt_eq hM' (rep S (pt' S s X).1) X (pt' S s X).2 (hrep S (pt' S s X).1) (by rw [(pt' S s X).2])
  · intro v hv
    refine hu_uniq v ?_
    intro C _ _ z hz
    have := hv C (z ≫ πM') (rep C z)
    rw [hrep C z] at this
    exact this

end D2GaloisActionAux

open D2GaloisActionAux in

theorem solution
    (g d n : ℕ) (Q : ∀ (S : Type) [CommRing S], PolarisedAbelianScheme g d n S → Prop)
    (hQbc : ∀ {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
      (u : PolarisedAbelianScheme g d n S) (u' : PolarisedAbelianScheme g d n S'),
      PolarisedAbelianScheme.IsPullback φ u u' → Q S u → Q S' u')
    (𝒪 : Type) [CommRing 𝒪] (𝒪' : Type) [CommRing 𝒪'] [Algebra 𝒪 𝒪']
    (G : Type) [Group G] [Finite G] (τ : G →* (𝒪' ≃ₐ[𝒪] 𝒪'))

    (hgal : ∀ (S : Type) [CommRing S] (s₁ s₂ : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪')),
      s₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 𝒪')) = s₂ ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 𝒪')) →
      ∃ (k : ℕ) (r : Fin k → S), Ideal.span (Set.range r) = ⊤ ∧ ∀ i : Fin k, ∃ σ : G,
        Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i)))) ≫ s₂ =
          Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i)))) ≫ s₁ ≫
            Spec.map (CommRingCat.ofHom ((τ σ : 𝒪' ≃ₐ[𝒪] 𝒪') : 𝒪' →+* 𝒪')))
    (M' : Scheme.{0}) (πM' : M' ⟶ Spec (CommRingCat.of 𝒪'))
    (pt' : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪')),
      PolarisedAbelianScheme.Satisfying g d n Q S → SchemeHomOver s πM')
    (hM' : PolarisedAbelianScheme.Satisfying.IsFineModuli g d n Q M' πM' pt') :
    ∃ ρ : G → (M' ≅ M'),
      (ρ 1).hom = 𝟙 M' ∧ (∀ σ σ' : G, (ρ (σ * σ')).hom = (ρ σ).hom ≫ (ρ σ').hom) ∧
      (∀ σ : G, (ρ σ).hom ≫ πM' = πM' ≫ Spec.map (CommRingCat.ofHom ((τ σ : 𝒪' ≃ₐ[𝒪] 𝒪') : 𝒪' →+* 𝒪'))) ∧
      (∀ (σ : G) (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪'))
        (X : PolarisedAbelianScheme.Satisfying g d n Q S),
        (pt' S s X).1 ≫ (ρ σ).hom = (pt' S (s ≫ Spec.map (CommRingCat.ofHom ((τ σ : 𝒪' ≃ₐ[𝒪] 𝒪') : 𝒪' →+* 𝒪'))) X).1) ∧
      (∀ (M : Scheme.{0}) (q : M' ⟶ M), (∀ σ : G, (ρ σ).hom ≫ q = q) →
        ∀ (S : Type) [CommRing S] (s₁ s₂ : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪')),
          s₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 𝒪')) = s₂ ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 𝒪')) →
          ∀ X : PolarisedAbelianScheme.Satisfying g d n Q S, (pt' S s₁ X).1 ≫ q = (pt' S s₂ X).1 ≫ q) := by
  classical

  have key := fun σ : G =>
    D2GaloisActionAux.exists_twist hM' hQbc (Spec.map (CommRingCat.ofHom ((τ σ : 𝒪' ≃ₐ[𝒪] 𝒪') : 𝒪' →+* 𝒪')))
  choose ρh hρπ hρpt hρuniq using key

  have ht1 : Spec.map (CommRingCat.ofHom ((τ 1 : 𝒪' ≃ₐ[𝒪] 𝒪') : 𝒪' →+* 𝒪')) = 𝟙 _ := by
    have : ((τ 1 : 𝒪' ≃ₐ[𝒪] 𝒪') : 𝒪' →+* 𝒪') = RingHom.id 𝒪' := by
      rw [map_one]; exact RingHom.ext fun _ => rfl
    rw [this, CommRingCat.ofHom_id, Spec.map_id]
  have htmul : ∀ σ σ' : G, Spec.map (CommRingCat.ofHom ((τ (σ * σ') : 𝒪' ≃ₐ[𝒪] 𝒪') : 𝒪' →+* 𝒪')) =
      Spec.map (CommRingCat.ofHom ((τ σ : 𝒪' ≃ₐ[𝒪] 𝒪') : 𝒪' →+* 𝒪')) ≫
        Spec.map (CommRingCat.ofHom ((τ σ' : 𝒪' ≃ₐ[𝒪] 𝒪') : 𝒪' →+* 𝒪')) := by
    intro σ σ'
    have : ((τ (σ * σ') : 𝒪' ≃ₐ[𝒪] 𝒪') : 𝒪' →+* 𝒪') =
        ((τ σ : 𝒪' ≃ₐ[𝒪] 𝒪') : 𝒪' →+* 𝒪').comp ((τ σ' : 𝒪' ≃ₐ[𝒪] 𝒪') : 𝒪' →+* 𝒪') := by
      rw [map_mul]; exact RingHom.ext fun _ => rfl
    rw [this, CommRingCat.ofHom_comp, Spec.map_comp]
  have hone : ρh 1 = 𝟙 M' := by
    symm
    refine hρuniq 1 (𝟙 M') fun S _ s X => ?_
    rw [Category.comp_id]
    exact D2GaloisActionAux.pt_congr (by rw [ht1, Category.comp_id]) X
  have hmul : ∀ σ σ' : G, ρh (σ * σ') = ρh σ ≫ ρh σ' := by
    intro σ σ'
    symm
    refine hρuniq (σ * σ') (ρh σ ≫ ρh σ') fun S _ s X => ?_
    rw [← Category.assoc, hρpt σ S s X, hρpt σ' S _ X]
    exact D2GaloisActionAux.pt_congr (by rw [htmul, Category.assoc]) X
  let ρ : G → (M' ≅ M') := fun σ =>
    { hom := ρh σ
      inv := ρh σ⁻¹
      hom_inv_id := by rw [← hmul, mul_inv_cancel, hone]
      inv_hom_id := by rw [← hmul, inv_mul_cancel, hone] }
  refine ⟨ρ, hone, hmul, hρπ, fun σ S _ s X => hρpt σ S s X, ?_⟩
  intro M q hq S _ s₁ s₂ h12 X
  obtain ⟨k, r, hr, hloc⟩ := hgal S s₁ s₂ h12
  refine Scheme.Cover.hom_ext
    (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of S) r hr).openCover _ _ fun i => ?_
  obtain ⟨σ, hσ⟩ := hloc i
  obtain ⟨Xi, hXi⟩ := D2GaloisActionAux.exists_isPullback hQbc (algebraMap S (Localization.Away (r i))) X
  have hpb := fun s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪') =>
    hM'.pt_pullback S (Localization.Away (r i)) (algebraMap S (Localization.Away (r i))) s _ rfl X Xi hXi
  change Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i)))) ≫ (pt' S s₁ X).1 ≫ q =
    Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i)))) ≫ (pt' S s₂ X).1 ≫ q
  calc Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i)))) ≫ (pt' S s₁ X).1 ≫ q
      = Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i)))) ≫ (pt' S s₁ X).1 ≫ (ρ σ).hom ≫ q := by
        rw [hq σ]
    _ = Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i)))) ≫
          (pt' S (s₁ ≫ Spec.map (CommRingCat.ofHom ((τ σ : 𝒪' ≃ₐ[𝒪] 𝒪') : 𝒪' →+* 𝒪'))) X).1 ≫ q := by
        rw [← Category.assoc (pt' S s₁ X).1, hρpt σ S s₁ X]
    _ = (pt' (Localization.Away (r i)) (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i)))) ≫
          s₁ ≫ Spec.map (CommRingCat.ofHom ((τ σ : 𝒪' ≃ₐ[𝒪] 𝒪') : 𝒪' →+* 𝒪'))) Xi).1 ≫ q := by
        rw [← Category.assoc, ← hpb]
    _ = (pt' (Localization.Away (r i)) (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i)))) ≫
          s₂) Xi).1 ≫ q := by
        rw [D2GaloisActionAux.pt_congr hσ.symm Xi]
    _ = Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r i)))) ≫ (pt' S s₂ X).1 ≫ q := by
        rw [hpb, Category.assoc]

end S_AlgebraicGeometry_PolarisedAbelianScheme_Satisfying_exists_aut_comp_pt_eq_and_comp_eq_of_isFineModuli_of_galois_of_isPullback
end P2MW
export P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_Satisfying_exists_aut_comp_pt_eq_and_comp_eq_of_isFineModuli_of_galois_of_isPullback (solution)
