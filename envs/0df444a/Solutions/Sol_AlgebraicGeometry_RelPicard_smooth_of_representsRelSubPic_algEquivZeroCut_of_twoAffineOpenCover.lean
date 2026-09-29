-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.smooth_of_representsRelSubPic_algEquivZeroCut_of_twoAffineOpenCover
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/4b16af62-3f76-5124-911e-1c1d94a1a051

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import Definitions.Def_JacJ1Iface
import Definitions.Def_CategoryTheory_OverTotalPresheaf
import Definitions.Def_AlgebraicGeometry_LocalRepresentabilityULift
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_of_squareZero_of_twoAffineOpenCover
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_smooth_of_representsRelSubPic_algEquivZeroCut_of_twoAffineOpenCover
p2m_attr_erase "instance" "AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField"
p2m_attr_erase "simp" "AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst"

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian

set_option autoImplicit false
set_option maxHeartbeats 6400000

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (𝒱 : C.TwoAffineOpenCover)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    [LocallyOfFiniteType D.toBase] :
    Smooth D.toBase := by
  haveI : IsLocallyNoetherian (Spec (CommRingCat.of R)) := inferInstance
  haveI hlfp : LocallyOfFinitePresentation D.toBase := inferInstance
  haveI : IsAffine (Spec (CommRingCat.of R)) := inferInstance
  refine HasRingHomProperty.of_source_openCover (P := @Smooth) D.P.affineCover ?_
  intro i
  haveI : IsAffine (D.P.affineCover.X i) := inferInstance
  haveI hlfp_i : LocallyOfFinitePresentation (D.P.affineCover.f i ≫ D.toBase) :=
    MorphismProperty.IsStableUnderComposition.comp_mem _ _ inferInstance hlfp
  set φ := ((D.P.affineCover.f i ≫ D.toBase).appTop).hom with hφ
  letI := φ.toAlgebra
  refine { formallySmooth := ?fsm, finitePresentation := ?fp }
  case fp =>
    exact (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)).mp hlfp_i
  case fsm =>
    refine Algebra.FormallySmooth.of_comp_surjective ?_
    intro B _ _ I hI2 ψ

    letI : Algebra R B := RingHom.toAlgebra
      ((algebraMap (Γ(Spec (CommRingCat.of R), ⊤)) B).comp
        (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    have hI_nil : I ≤ _root_.nilradical B := fun a ha =>
      ⟨2, by have h2 := Ideal.pow_mem_pow ha 2; rw [hI2] at h2; simpa using h2⟩
    have hι_comp : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R B)) =
        Spec.map (CommRingCat.ofHom (algebraMap R (B ⧸ I))) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    set ι : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (B ⧸ I))))
        (Spec.map (CommRingCat.ofHom (algebraMap R B))) :=
      ⟨Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)), hι_comp⟩ with hι_def

    let x₀ : Spec (CommRingCat.of (B ⧸ I)) ⟶ D.P.affineCover.X i :=
      Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ (D.P.affineCover.X i).isoSpec.inv
    have hx₀_over : (x₀ ≫ D.P.affineCover.f i) ≫ D.toBase =
        Spec.map (CommRingCat.ofHom (algebraMap R (B ⧸ I))) := by
      have hnat : (D.P.affineCover.X i).isoSpec.inv ≫ (D.P.affineCover.f i ≫ D.toBase) =
          Spec.map ((D.P.affineCover.f i ≫ D.toBase).appTop) ≫
            (Spec (CommRingCat.of R)).isoSpec.inv := by
        rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
        exact (Scheme.isoSpec_hom_naturality (D.P.affineCover.f i ≫ D.toBase)).symm
      simp only [x₀, Category.assoc]; rw [hnat, ← Category.assoc, ← Spec.map_comp]

      rw [show (Spec (CommRingCat.of R)).isoSpec.inv =
          Spec.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv from
          Scheme.isoSpec_Spec_inv (CommRingCat.of R), ← Spec.map_comp]
      congr 1

      ext x
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]

      have h1 : ψ.toRingHom (((D.P.affineCover.f i ≫ D.toBase).appTop).hom
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x)) =
          algebraMap (Γ(Spec (CommRingCat.of R), ⊤)) (B ⧸ I)
            ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x) := by
        rw [← hφ]; exact (ψ.commutes _).symm |>.symm
      rw [h1]
      rfl
    set g₀ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (B ⧸ I)))) D.toBase :=
      ⟨x₀ ≫ D.P.affineCover.f i, hx₀_over⟩ with hg₀_def

    set M := h.poincare.pullbackAlong g₀ with hM_def
    have hM_cut : FibrewiseAlgEquivZero M :=
      (algEquivZeroCut c ε).pullback_mem _ _ g₀ _ h.poincare_mem

    obtain ⟨M', hM'_iso⟩ : ∃ M' : RigidifiedLineBundle c ε
          (Spec.map (CommRingCat.ofHom (algebraMap R B))),
        Nonempty ((M'.pullbackAlong ι).L ≅ M.L) :=
      RigidifiedLineBundle.exists_of_squareZero_of_twoAffineOpenCover
        c ε 𝒱 I hI2 ι rfl M

    have hM'ι_cut : FibrewiseAlgEquivZero (M'.pullbackAlong ι) :=
      hM_cut.congr ⟨hM'_iso.some.symm⟩
    have hM'_cut : FibrewiseAlgEquivZero M' := by

      intro k _ _ s
      obtain ⟨s₀, hs₀⟩ : ∃ s₀ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (B ⧸ I)),
          s₀ ≫ ι.1 = s := by
        set φk := (Spec.preimage s).hom with hφk'
        have hker : ∀ a ∈ I, φk a = 0 := fun a ha =>
          isNilpotent_iff_eq_zero.mp ((mem_nilradical.mp (hI_nil ha)).map φk)
        refine ⟨Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift I φk hker)), ?_⟩
        rw [show ι.1 = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) from rfl,
          ← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.lift_comp_mk]
        exact Spec.map_preimage s
      subst hs₀
      have hψ' : pullback.snd c _ ≫ ι.1 = baseChangeSnd c ι ≫ pullback.snd c _ := by
        simp only [baseChangeSnd, pullback.lift_snd]
      let e : Limits.pullback (pullback.snd c
            (Spec.map (CommRingCat.ofHom (algebraMap R (B ⧸ I))))) s₀ ⟶
          Limits.pullback (pullback.snd c
            (Spec.map (CommRingCat.ofHom (algebraMap R B)))) (s₀ ≫ ι.1) :=
        pullback.map _ _ _ _ (baseChangeSnd c ι) (𝟙 _) ι.1 hψ' (by simp)
      have he : e ≫ fibreAt c _ (s₀ ≫ ι.1) = fibreAt c _ s₀ := by
        simp only [e, fibreAt, pullback.lift_snd, Category.comp_id]
      have hfst : e ≫ pullback.fst _ _ = pullback.fst _ _ ≫ baseChangeSnd c ι := by
        simp only [e, pullback.lift_fst]
      have hsnd : e ≫ pullback.snd _ _ = pullback.snd _ _ := by
        simp only [e, pullback.lift_snd, Category.comp_id]
      have hp : IsPullback (baseChangeSnd c ι) (pullback.snd c _) (pullback.snd c _) ι.1 := by
        refine IsPullback.of_right ?_ hψ'.symm (IsPullback.of_hasPullback c _)
        simp only [baseChangeSnd, pullback.lift_fst, Category.comp_id]
        convert IsPullback.of_hasPullback c
          (Spec.map (CommRingCat.ofHom (algebraMap R (B ⧸ I)))) using 2 <;>
          (try exact ι.2)
      have hpaste : IsPullback (pullback.fst _ _ ≫ baseChangeSnd c ι) (pullback.snd _ s₀)
          (pullback.snd c _) (s₀ ≫ ι.1) :=
        (IsPullback.of_hasPullback _ s₀).paste_horiz hp
      haveI : IsIso e := by
        have heq : e = hpaste.isoPullback.hom := by
          apply pullback.hom_ext
          · rw [hfst, IsPullback.isoPullback_hom_fst]
          · rw [hsnd, IsPullback.isoPullback_hom_snd]
        exact heq ▸ inferInstance
      refine IsAlgEquivZero.of_iso ?_
        ((hM'ι_cut k s₀).pullback (inv e) (by rw [IsIso.inv_comp_eq, he]))
      refine (Scheme.Modules.pullbackComp _ _).app _ ≪≫
        (Scheme.Modules.pullbackComp _ _).app M'.L ≪≫
        (Scheme.Modules.pullbackCongr ?_).app M'.L
      rw [Category.assoc, ← hfst, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

    set g' := h.classify _ M' hM'_cut with hg'_def
    have hg'_comp : postComp g' ι = g₀ := by
      apply h.ext_of_iso

      refine ⟨?_⟩
      calc (h.poincare.pullbackAlong (postComp g' ι)).L
          ≅ (Scheme.Modules.pullback (baseChangeSnd c (postComp g' ι))).obj h.poincare.L := Iso.refl _
        _ ≅ (Scheme.Modules.pullback (baseChangeSnd c ι ≫ baseChangeSnd c g')).obj h.poincare.L :=
            (Scheme.Modules.pullbackCongr (baseChangeSnd_comp c g' ι).symm).app _
        _ ≅ (Scheme.Modules.pullback (baseChangeSnd c ι)).obj
              ((Scheme.Modules.pullback (baseChangeSnd c g')).obj h.poincare.L) :=
            ((Scheme.Modules.pullbackComp _ _).app _).symm
        _ ≅ (Scheme.Modules.pullback (baseChangeSnd c ι)).obj M'.L :=
            (Scheme.Modules.pullback _).mapIso (h.classify_spec _ M' hM'_cut).some
        _ ≅ M.L := hM'_iso.some
        _ ≅ (h.poincare.pullbackAlong g₀).L := Iso.refl _

    have hg₀_eq : g₀.1 = ι.1 ≫ g'.1 := by
      have := congrArg Subtype.val hg'_comp; simp only [postComp] at this; exact this.symm
    have hv_check : x₀ ≫ D.P.affineCover.f i =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ g'.1 := by
      have h1 : (↑g₀ : _ ⟶ D.P) = x₀ ≫ D.P.affineCover.f i := by simp [hg₀_def]
      have h2 : (↑ι : _ ⟶ _) = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := rfl
      rw [← h1, ← h2]; exact hg₀_eq
    obtain ⟨w', hw'⟩ : ∃ w' : Spec (CommRingCat.of B) ⟶ D.P.affineCover.X i,
        w' ≫ D.P.affineCover.f i = g'.1 := by

      have hsurj : Function.Surjective
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).base := by
        show Function.Surjective (PrimeSpectrum.comap (Ideal.Quotient.mk I))
        exact (PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical hI_nil).2
      have hrange : Set.range (g'.1 : _ ⟶ D.P).base ⊆
          Set.range (D.P.affineCover.f i).base := by
        rintro y ⟨p, rfl⟩
        obtain ⟨q, rfl⟩ := hsurj p
        refine ⟨x₀.base q, ?_⟩
        have := congrArg (fun f => (Scheme.Hom.toLRSHom f).base q) hv_check
        simpa using this
      exact ⟨IsOpenImmersion.lift (D.P.affineCover.f i) g'.1 hrange,
        IsOpenImmersion.lift_fac (D.P.affineCover.f i) g'.1 hrange⟩

    have hx₀_eq : x₀ = ι.1 ≫ w' := by
      haveI : Mono (D.P.affineCover.f i) := inferInstance
      rw [← cancel_mono (D.P.affineCover.f i)]
      simp only [Category.assoc, hw', ← hg₀_eq, hg₀_def]
    have hw'_over : w' ≫ (D.P.affineCover.f i ≫ D.toBase) =
        Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
      rw [← Category.assoc, hw']; exact g'.2
    refine ⟨⟨(Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom.comp w'.appTop.hom, fun r => ?_⟩, ?_⟩
    ·
      show (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom (w'.appTop.hom (φ r)) =
        algebraMap (Γ(Spec (CommRingCat.of R), ⊤)) B r
      have happ : w'.appTop.hom (φ r) =
          (Spec.map (CommRingCat.ofHom (algebraMap R B))).appTop.hom r := by
        have := congrArg (fun f => (Scheme.Hom.appTop f).hom r) hw'_over
        simp [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, ← hφ] at this
        exact this
      rw [happ]
      have hnat2 := congrArg (fun g => g.hom r)
        (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R B)))
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hnat2
      rw [hnat2]
      show ((algebraMap (Γ(Spec (CommRingCat.of R), ⊤)) B).comp
          (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
          ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r) = _
      simp only [RingHom.comp_apply]
      congr 1
      exact congrArg (fun g => CommRingCat.Hom.hom g r)
        (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id
    ·
      apply AlgHom.ext; intro a
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, AlgHom.coe_mk,
        RingHom.coe_comp, Function.comp_apply]

      have hx₀_app : x₀.appTop.hom a = (ι.1).appTop.hom (w'.appTop.hom a) := by
        have := congrArg (fun f => (Scheme.Hom.appTop f).hom a) hx₀_eq
        simpa [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] using this

      have hι_nat := congrArg (fun g => g.hom (w'.appTop.hom a))
        (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk I)))
      simp only [hι_def, CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hι_nat
      rw [show (↑ι : _ ⟶ _) = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) from rfl] at hx₀_app
      rw [← hι_nat, ← hx₀_app]

      simp only [x₀, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
      have hnat3 := congrArg (fun g => g.hom
          (((D.P.affineCover.X i).isoSpec.inv.appTop).hom a))
        (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ.toRingHom))
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hnat3
      rw [hnat3]

      have htri : (D.P.affineCover.X i).isoSpec.inv.appTop ≫
          (Scheme.ΓSpecIso (Γ(D.P.affineCover.X i, ⊤))).hom = 𝟙 _ := by
        rw [show (Scheme.ΓSpecIso (Γ(D.P.affineCover.X i, ⊤))).hom =
            (D.P.affineCover.X i).isoSpec.hom.appTop from
            ((D.P.affineCover.X i).toSpecΓ_appTop).symm,
          ← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]
      have htria : (Scheme.ΓSpecIso (Γ(D.P.affineCover.X i, ⊤))).hom.hom
          (((D.P.affineCover.X i).isoSpec.inv.appTop).hom a) = a := by
        have := congrArg (fun g => CommRingCat.Hom.hom g a) htri
        simpa using this

      change ψ.toRingHom ((Scheme.ΓSpecIso (Γ(D.P.affineCover.X i, ⊤))).hom.hom
        (((D.P.affineCover.X i).isoSpec.inv.appTop).hom a)) = ψ a
      rw [htria]; rfl

end S_AlgebraicGeometry_RelPicard_smooth_of_representsRelSubPic_algEquivZeroCut_of_twoAffineOpenCover
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_smooth_of_representsRelSubPic_algEquivZeroCut_of_twoAffineOpenCover (solution)
