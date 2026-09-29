-- Prove2me | solution 1 for AlgebraicGeometry.PolarisedAbelianScheme.exists_isAlgClosed_principalRoot_thetaPt_of_rootedSymmetricOfType
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/e34f9edc-6100-5e6a-87ce-c72c9a8d6227

import Definitions.Def_AlgebraicGeometry_ThetaGroupLaw
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType
import Theorems.Thm_AlgebraicGeometry_Polarisation_ThetaPt_exists_monoidHom_pt_comp_eq_act_eq_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Polarisation_ThetaPt_ofScalar_act
import Theorems.Thm_AlgebraicGeometry_Polarisation_ThetaPt_mul_act
import Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_thetaPt_eq_of_pt_eq_of_forall_act_eq
import Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_principalRoot_over_of_ringHom_of_forall_exists_principalRoot
import Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_eq_comp_of_memKernel_of_isOfType_of_isAlgClosed
import Theorems.Thm_Module_FaithfullyFlat_exists_ringHom_isAlgClosed_comp_algebraMap_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_isAlgClosed_principalRoot_thetaPt_of_rootedSymmetricOfType
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
p2m_open_scoped "BigOperators CategoryTheory.MonoidalCategory"

noncomputable section

namespace ENLAux

theorem mul_val_congr {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of S)} (h : t₁ = t₂)
    (P Q : SchemeHomOver t₁ f) (P' Q' : SchemeHomOver t₂ f) (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) :
    (L.mul t₁ P Q).1 = (L.mul t₂ P' Q').1 := by
  subst h
  obtain rfl : P = P' := Subtype.ext hP
  obtain rfl : Q = Q' := Subtype.ext hQ
  rfl

theorem injective_transport {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} {ι : Type}
    {R R' : Type} [CommRing R] [CommRing R'] (tR : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    (tR' : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of S)) (ψ : R →+* R') (hr : Spec.map (CommRingCat.ofHom ψ) ≫ tR = tR')
    (x : ι → SchemeHomOver tR f) (x' : ι → SchemeHomOver tR' f) (hx' : ∀ h, (x' h).1 = Spec.map (CommRingCat.ofHom ψ) ≫ (x h).1)
    [Epi (Spec.map (CommRingCat.ofHom ψ))] (hinj : Function.Injective x) : Function.Injective x' := by
  intro h h' e
  apply hinj
  apply Subtype.ext
  rw [← cancel_epi (Spec.map (CommRingCat.ofHom ψ)), ← hx', ← hx', e]

theorem transport_comm {g d n : ℕ} {ι : Type}
    {S : Type} [CommRing S] (u : PolarisedAbelianScheme g d n S)
    {R R' : Type} [CommRing R] [CommRing R'] (tR : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    (tR' : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of S)) (ψ : R →+* R')
    (hr : Spec.map (CommRingCat.ofHom ψ) ≫ tR = tR')
    (θ₀ : ι → ThetaPt u.f u.L u.pol tR) (θ : ThetaPt u.f u.L u.pol tR)
    (hcomm : ∀ (h : ι) (s : Γ((Scheme.Modules.pullback (pullback.fst u.f tR)).obj u.pol, ⊤)),
      θ.act ((θ₀ h).act s) = (θ₀ h).act (θ.act s)) :
    ∃ (θL : ι → ThetaPt u.f u.L u.pol tR') (θ' : ThetaPt u.f u.L u.pol tR'),
      (∀ h, (θL h).pt.1 = Spec.map (CommRingCat.ofHom ψ) ≫ (θ₀ h).pt.1) ∧
      (θ'.pt.1 = Spec.map (CommRingCat.ofHom ψ) ≫ θ.pt.1) ∧
      (∀ (h : ι) (s : Γ((Scheme.Modules.pullback (pullback.fst u.f tR')).obj u.pol, ⊤)),
        θ'.act ((θL h).act s) = (θL h).act (θ'.act s)) := by
  classical
  have hid : Spec.map (CommRingCat.ofHom (RingHom.id S)) = 𝟙 _ := by rw [CommRingCat.ofHom_id, Spec.map_id]
  haveI : IsIso (Spec.map (CommRingCat.ofHom (RingHom.id S))) := by rw [hid]; infer_instance
  have hg : IsPullback (𝟙 u.A) u.f u.f (Spec.map (CommRingCat.ofHom (RingHom.id S))) :=
    IsPullback.of_horiz_isIso ⟨by rw [hid, Category.id_comp, Category.comp_id]⟩
  have hmul : ∀ {T : Scheme.{0}} (t'' : T ⟶ Spec (CommRingCat.of S)) (a b : SchemeHomOver t'' u.f),
      (u.L.mul t'' a b).1 ≫ 𝟙 u.A =
        (u.L.mul (t'' ≫ Spec.map (CommRingCat.ofHom (RingHom.id S)))
          ⟨a.1 ≫ 𝟙 u.A, by rw [Category.assoc, hg.w, ← Category.assoc, a.2]⟩
          ⟨b.1 ≫ 𝟙 u.A, by rw [Category.assoc, hg.w, ← Category.assoc, b.2]⟩).1 := by
    intro T t'' a b
    rw [Category.comp_id]
    exact mul_val_congr u.L (by rw [hid, Category.comp_id]) a b _ _ (Category.comp_id _).symm (Category.comp_id _).symm
  have hr' : Spec.map (CommRingCat.ofHom ψ) ≫ tR = tR' ≫ Spec.map (CommRingCat.ofHom (RingHom.id S)) := by
    rw [hid, Category.comp_id]; exact hr
  let b : pullback u.f tR' ⟶ pullback u.f tR :=
    pullback.lift (pullback.fst u.f tR') (pullback.snd u.f tR' ≫ Spec.map (CommRingCat.ofHom ψ))
      (by rw [pullback.condition, Category.assoc, hr])
  have hb₁ : b ≫ pullback.fst u.f tR = pullback.fst u.f tR' ≫ 𝟙 u.A := by rw [pullback.lift_fst, Category.comp_id]
  have hb₂ : b ≫ pullback.snd u.f tR = pullback.snd u.f tR' ≫ Spec.map (CommRingCat.ofHom ψ) := pullback.lift_snd _ _ _
  let c : (Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback (pullback.fst u.f tR)).obj u.pol) ≅
      (Scheme.Modules.pullback (pullback.fst u.f tR')).obj u.pol :=
    (Scheme.Modules.pullbackComp b (pullback.fst u.f tR)).app u.pol ≪≫
      (Scheme.Modules.pullbackCongr (show b ≫ pullback.fst u.f tR = pullback.fst u.f tR' from pullback.lift_fst _ _ _)).app u.pol
  obtain ⟨β, hβpt, -, -, -⟩ :=
    AlgebraicGeometry.Polarisation.ThetaPt.exists_monoidHom_pt_comp_eq_act_eq_of_isPullback (RingHom.id S) u.L u.L (𝟙 u.A) hg
      hmul u.pol u.pol tR tR' ψ hr' b hb₁ hb₂ c
  have hgrp : ∀ h, θ * θ₀ h = θ₀ h * θ := by
    intro h
    apply AlgebraicGeometry.PolarisedAbelianScheme.thetaPt_eq_of_pt_eq_of_forall_act_eq u
    · rw [ThetaPt.mul_pt, ThetaPt.mul_pt]; exact u.comm tR _ _
    · intro s; rw [ThetaPt.mul_act, ThetaPt.mul_act, hcomm]
  refine ⟨fun h => β (θ₀ h), β θ, fun h => ?_, ?_, ?_⟩
  · have := hβpt (θ₀ h); rw [Category.comp_id] at this; exact this
  · have := hβpt θ; rw [Category.comp_id] at this; exact this
  · intro h s
    rw [← ThetaPt.mul_act, ← ThetaPt.mul_act, ← map_mul, ← map_mul, hgrp]

theorem epi_specMap_of_field {K L : Type} [Field K] [Field L] (ψ : K →+* L) : Epi (Spec.map (CommRingCat.ofHom ψ)) := by
  have hff : (CommRingCat.ofHom ψ).hom.FaithfullyFlat := by
    letI : Algebra K L := ψ.toAlgebra
    change (algebraMap K L).FaithfullyFlat
    rw [RingHom.faithfullyFlat_algebraMap_iff]
    infer_instance
  obtain ⟨h1, h2⟩ := (AlgebraicGeometry.flat_and_surjective_SpecMap_iff (CommRingCat.ofHom ψ)).mpr hff
  exact Flat.epi_of_flat_of_surjective _

end ENLAux

theorem solution
    {g d n : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (hδd : ∏ i, δ i = d)
    {S : Type} [CommRing S] (hd : IsUnit ((d : ℕ) : S))
    (u : PolarisedAbelianScheme g d n S) (hu : PolarisedAbelianScheme.RootedSymmetricOfType δ S u)
    {K : Type} [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of S))
    (x : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → SchemeHomOver t u.f)
    (hx0 : x 0 = u.L.one t) (hx : ∀ h h' : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))), x (h + h') = u.L.mul t (x h) (x h'))
    (hxinj : Function.Injective x)
    (hxK : ∀ y : SchemeHomOver t u.f, Polarisation.MemKernel u.f u.L u.pol t y → ∃ h : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))), y = x h)
    (θ₀ : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → ThetaPt u.f u.L u.pol t) (hθ₀ : ∀ h, (θ₀ h).pt = x h)
    (θ : ThetaPt u.f u.L u.pol t)
    (hcomm : ∀ (h : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i)))) (s : Γ((Scheme.Modules.pullback (pullback.fst u.f t)).obj u.pol, ⊤)),
      θ.act ((θ₀ h).act s) = (θ₀ h).act (θ.act s)) :
    ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (ψ : K →+* L), Epi (Spec.map (CommRingCat.ofHom ψ)) ∧
    ∃ (L' : RelativeGroupLaw L (pullback.snd u.f (Spec.map (CommRingCat.ofHom ψ) ≫ t)))
      (_ : ∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of L)) (P Q : SchemeHomOver t' (pullback.snd u.f (Spec.map (CommRingCat.ofHom ψ) ≫ t))),
        (L'.mul t' P Q).1 ≫ pullback.fst u.f (Spec.map (CommRingCat.ofHom ψ) ≫ t) =
          (u.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom ψ) ≫ t))
            ⟨P.1 ≫ pullback.fst u.f (Spec.map (CommRingCat.ofHom ψ) ≫ t), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ pullback.fst u.f (Spec.map (CommRingCat.ofHom ψ) ≫ t), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1)
      (𝓛₀ : (pullback u.f (Spec.map (CommRingCat.ofHom ψ) ≫ t)).Modules) (a b : ℕ),
      1 ≤ a + b ∧ Scheme.Modules.IsInvertible 𝓛₀ ∧
      Polarisation.KernelTrivial (pullback.snd u.f (Spec.map (CommRingCat.ofHom ψ) ≫ t)) L' 𝓛₀ ∧
      Polarisation.LocIsoOnBase (pullback.snd u.f (Spec.map (CommRingCat.ofHom ψ) ≫ t))
        ((Scheme.Modules.pullback (pullback.fst u.f (Spec.map (CommRingCat.ofHom ψ) ≫ t))).obj u.pol)
        (Scheme.Modules.tpow 𝓛₀ a ⊗ Scheme.Modules.tpow ((Scheme.Modules.pullback (Polarisation.negMor (pullback.snd u.f (Spec.map (CommRingCat.ofHom ψ) ≫ t)) L')).obj 𝓛₀) b) ∧
    ∃ (xL : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → SchemeHomOver (Spec.map (CommRingCat.ofHom ψ) ≫ t) u.f)
      (θL : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))) → ThetaPt u.f u.L u.pol (Spec.map (CommRingCat.ofHom ψ) ≫ t)) (θ' : ThetaPt u.f u.L u.pol (Spec.map (CommRingCat.ofHom ψ) ≫ t)),
      (∀ h, (xL h).1 = Spec.map (CommRingCat.ofHom ψ) ≫ (x h).1) ∧
      xL 0 = u.L.one _ ∧ (∀ h h' : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i))), xL (h + h') = u.L.mul _ (xL h) (xL h')) ∧ Function.Injective xL ∧
      (∀ y : SchemeHomOver (Spec.map (CommRingCat.ofHom ψ) ≫ t) u.f, Polarisation.MemKernel u.f u.L u.pol _ y → ∃ h, y = xL h) ∧
      (∀ h, (θL h).pt = xL h) ∧ (θ'.pt.1 = Spec.map (CommRingCat.ofHom ψ) ≫ θ.pt.1) ∧
      (∀ (h : (((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i)))) (s : Γ((Scheme.Modules.pullback (pullback.fst u.f (Spec.map (CommRingCat.ofHom ψ) ≫ t))).obj u.pol, ⊤)), θ'.act ((θL h).act s) = (θL h).act (θ'.act s)) := by
  classical
  obtain ⟨-, hoft, hroot⟩ := hu
  obtain ⟨S', instS', instAlg, hff, hrootS'⟩ := hroot

  have ht : Spec.map (Spec.preimage t) = t := Spec.map_preimage t

  obtain ⟨L, instL, instAC, ψ, σ, hσ⟩ :=
    Module.FaithfullyFlat.exists_ringHom_isAlgClosed_comp_algebraMap_eq S' K (Spec.preimage t).hom
  haveI hepi : Epi (Spec.map (CommRingCat.ofHom ψ)) := ENLAux.epi_specMap_of_field ψ

  have htR : Spec.map (CommRingCat.ofHom σ) ≫ Spec.map (CommRingCat.ofHom (algebraMap S S')) =
      Spec.map (CommRingCat.ofHom ψ) ≫ t := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hσ, CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, ht]
  obtain ⟨LR, hLR, 𝓛₀, a, b, hab, hinv, hker, hloc⟩ :=
    AlgebraicGeometry.PolarisedAbelianScheme.exists_principalRoot_over_of_ringHom_of_forall_exists_principalRoot u S' hrootS'
      σ (Spec.map (CommRingCat.ofHom ψ) ≫ t) htR

  obtain ⟨θL, θ', hθLpt, hθ'pt, hcommL⟩ :=
    ENLAux.transport_comm u t (Spec.map (CommRingCat.ofHom ψ) ≫ t) ψ rfl θ₀ θ hcomm
  refine ⟨L, instL, instAC, ψ, hepi, LR, hLR, 𝓛₀, a, b, hab, hinv, hker, hloc,
    fun h => schemeHomOverComp (Spec.map (CommRingCat.ofHom ψ)) rfl (x h), θL, θ', fun h => rfl, ?_, ?_, ?_, ?_, ?_, hθ'pt, hcommL⟩
  · change schemeHomOverComp (Spec.map (CommRingCat.ofHom ψ)) rfl (x 0) = _
    rw [hx0]; exact u.L.one_natural _ _ _ rfl
  · intro h h'
    change schemeHomOverComp (Spec.map (CommRingCat.ofHom ψ)) rfl (x (h + h')) =
      u.L.mul _ (schemeHomOverComp (Spec.map (CommRingCat.ofHom ψ)) rfl (x h))
        (schemeHomOverComp (Spec.map (CommRingCat.ofHom ψ)) rfl (x h'))
    rw [hx]; exact u.L.mul_natural _ _ _ rfl _ _
  · exact ENLAux.injective_transport t _ ψ rfl x _ (fun h => rfl) hxinj
  · intro y hy
    obtain ⟨h, hh⟩ := AlgebraicGeometry.PolarisedAbelianScheme.exists_eq_comp_of_memKernel_of_isOfType_of_isAlgClosed δ u hoft
      t x hxK ψ y hy
    exact ⟨h, Subtype.ext hh⟩
  · intro h
    apply Subtype.ext
    rw [hθLpt h, hθ₀ h]
    rfl

end

end S_AlgebraicGeometry_PolarisedAbelianScheme_exists_isAlgClosed_principalRoot_thetaPt_of_rootedSymmetricOfType
end P2MW
export P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_isAlgClosed_principalRoot_thetaPt_of_rootedSymmetricOfType (solution)
