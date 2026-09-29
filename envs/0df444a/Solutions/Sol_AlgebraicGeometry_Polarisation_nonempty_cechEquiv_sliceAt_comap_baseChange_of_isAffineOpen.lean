-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.nonempty_cechEquiv_sliceAt_comap_baseChange_of_isAffineOpen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/f4d9a15e-996f-5a18-902d-daa0871e86a3

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso_pullback_of_isIso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_nonempty_cechEquiv_sliceAt_comap_baseChange_of_isAffineOpen
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem solution
    (K : Type) [Field K] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of K)) [IsSeparated f]
    (F : (pullback f f).Modules) (hF : Scheme.Modules.IsInvertible F)
    (𝒦 : A.OrderedAffineCover) (V : A.Opens) (hV : IsAffineOpen V)
    (B : Type) [CommRing B] [Algebra Γ(A, V) B]
    (t : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t f)
    (hx : x.1 = Scheme.TwoAffineOpenCover.specMap Γ(A, V) B ≫ hV.fromSpec) :
    letI tV : Spec (CommRingCat.of Γ(A, V)) ⟶ Spec (CommRingCat.of K) := hV.fromSpec ≫ f
    letI xV : SchemeHomOver tV f := ⟨hV.fromSpec, rfl⟩
    letI π : pullback f tV ⟶ Spec (CommRingCat.of Γ(A, V)) := pullback.snd f tV
    letI MV : (pullback f tV).Modules := (Scheme.Modules.pullback (sliceAt f xV)).obj F
    letI _ : IsAffineHom (pullback.fst f tV) := MorphismProperty.pullback_fst _ _ inferInstance
    letI _ : IsAffineHom (pullback.fst f t) := MorphismProperty.pullback_fst _ _ inferInstance
    letI 𝒰 : (pullback f tV).OrderedAffineCover := 𝒦.comap (pullback.fst f tV)
    letI G := OModulePresheaf.ofModules (pullback.snd f t) ((Scheme.Modules.pullback (sliceAt f x)).obj F)
    letI G' := OModulePresheaf.ofModules (pullback.snd π (Scheme.TwoAffineOpenCover.specMap Γ(A, V) B))
      ((Scheme.Modules.pullback (pullback.fst π (Scheme.TwoAffineOpenCover.specMap Γ(A, V) B))).obj MV)
    Nonempty (G.H0 (𝒦.comap (pullback.fst f t)) ≃ₗ[B] G'.H0 (𝒰.baseChange π B)) ∧
      ∀ i : ℕ, Nonempty (G.HSucc (𝒦.comap (pullback.fst f t)) i ≃ₗ[B] G'.HSucc (𝒰.baseChange π B) i) := by
  classical
  obtain ⟨x1, hx1⟩ := x
  subst hx1
  simp only at hx
  subst hx
  haveI : IsAffineHom (pullback.fst f (hV.fromSpec ≫ f)) := MorphismProperty.pullback_fst _ _ inferInstance
  haveI : IsAffineHom (pullback.fst f (((Scheme.TwoAffineOpenCover.specMap Γ(A, V) B) ≫ hV.fromSpec) ≫ f)) := MorphismProperty.pullback_fst _ _ inferInstance

  let e1 : pullback f (((Scheme.TwoAffineOpenCover.specMap Γ(A, V) B) ≫ hV.fromSpec) ≫ f) ≅ pullback f ((Scheme.TwoAffineOpenCover.specMap Γ(A, V) B) ≫ (hV.fromSpec ≫ f)) :=
    pullback.congrHom rfl (Category.assoc _ _ _)
  let e2 : pullback (pullback.snd f (hV.fromSpec ≫ f)) (Scheme.TwoAffineOpenCover.specMap Γ(A, V) B) ≅ pullback f ((Scheme.TwoAffineOpenCover.specMap Γ(A, V) B) ≫ (hV.fromSpec ≫ f)) :=
    pullbackLeftPullbackSndIso f (hV.fromSpec ≫ f) (Scheme.TwoAffineOpenCover.specMap Γ(A, V) B)
  let Φ : pullback f (((Scheme.TwoAffineOpenCover.specMap Γ(A, V) B) ≫ hV.fromSpec) ≫ f) ⟶ pullback (pullback.snd f (hV.fromSpec ≫ f)) (Scheme.TwoAffineOpenCover.specMap Γ(A, V) B) := e1.hom ≫ e2.inv
  haveI : IsIso Φ := inferInstance
  have hΦsnd : Φ ≫ pullback.snd (pullback.snd f (hV.fromSpec ≫ f)) (Scheme.TwoAffineOpenCover.specMap Γ(A, V) B) = pullback.snd f (((Scheme.TwoAffineOpenCover.specMap Γ(A, V) B) ≫ hV.fromSpec) ≫ f) := by
    simp [Φ, e1, e2, pullback.congrHom, pullback.map]
    exact pullback.lift_snd _ _ _
  have hΦfst : Φ ≫ pullback.fst (pullback.snd f (hV.fromSpec ≫ f)) (Scheme.TwoAffineOpenCover.specMap Γ(A, V) B) ≫ pullback.fst f (hV.fromSpec ≫ f) =
      pullback.fst f (((Scheme.TwoAffineOpenCover.specMap Γ(A, V) B) ≫ hV.fromSpec) ≫ f) := by
    simp [Φ, e1, e2, pullback.congrHom, pullback.map]
    exact pullback.lift_fst _ _ _

  have hslice : sliceAt f (⟨(Scheme.TwoAffineOpenCover.specMap Γ(A, V) B) ≫ hV.fromSpec, rfl⟩ : SchemeHomOver (((Scheme.TwoAffineOpenCover.specMap Γ(A, V) B) ≫ hV.fromSpec) ≫ f) f) = Φ ≫ pullback.fst (pullback.snd f (hV.fromSpec ≫ f)) (Scheme.TwoAffineOpenCover.specMap Γ(A, V) B) ≫ sliceAt f (⟨hV.fromSpec, rfl⟩ : SchemeHomOver (hV.fromSpec ≫ f) f) := by
    apply pullback.hom_ext
    · simp only [sliceAt, pullback.lift_fst, Category.assoc]
      rw [hΦfst]
    · simp only [sliceAt, pullback.lift_snd, Category.assoc, pullback.condition_assoc]
      rw [← hΦsnd]
      simp only [Category.assoc]

  have hN' : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback (pullback.fst (pullback.snd f (hV.fromSpec ≫ f)) (Scheme.TwoAffineOpenCover.specMap Γ(A, V) B))).obj
      ((Scheme.Modules.pullback (sliceAt f (⟨hV.fromSpec, rfl⟩ : SchemeHomOver (hV.fromSpec ≫ f) f))).obj F)) := (hF.pullback _).pullback _
  let e : (Scheme.Modules.pullback (sliceAt f (⟨(Scheme.TwoAffineOpenCover.specMap Γ(A, V) B) ≫ hV.fromSpec, rfl⟩ : SchemeHomOver (((Scheme.TwoAffineOpenCover.specMap Γ(A, V) B) ≫ hV.fromSpec) ≫ f) f))).obj F ≅
      (Scheme.Modules.pullback Φ).obj ((Scheme.Modules.pullback (pullback.fst (pullback.snd f (hV.fromSpec ≫ f)) (Scheme.TwoAffineOpenCover.specMap Γ(A, V) B))).obj
        ((Scheme.Modules.pullback (sliceAt f (⟨hV.fromSpec, rfl⟩ : SchemeHomOver (hV.fromSpec ≫ f) f))).obj F)) :=
    (Scheme.Modules.pullbackCongr hslice).app F ≪≫
      ((Scheme.Modules.pullbackComp Φ (pullback.fst (pullback.snd f (hV.fromSpec ≫ f)) (Scheme.TwoAffineOpenCover.specMap Γ(A, V) B) ≫ sliceAt f (⟨hV.fromSpec, rfl⟩ : SchemeHomOver (hV.fromSpec ≫ f) f))).app F).symm ≪≫
      (Scheme.Modules.pullback Φ).mapIso
        (((Scheme.Modules.pullbackComp (pullback.fst (pullback.snd f (hV.fromSpec ≫ f)) (Scheme.TwoAffineOpenCover.specMap Γ(A, V) B)) (sliceAt f (⟨hV.fromSpec, rfl⟩ : SchemeHomOver (hV.fromSpec ≫ f) f))).app F).symm)

  have key : ∀ (q : pullback f (((Scheme.TwoAffineOpenCover.specMap Γ(A, V) B) ≫ hV.fromSpec) ≫ f) ⟶ Spec (CommRingCat.of B)),
      q = Φ ≫ pullback.snd (pullback.snd f (hV.fromSpec ≫ f)) (Scheme.TwoAffineOpenCover.specMap Γ(A, V) B) →
      Nonempty ((OModulePresheaf.ofModules q ((Scheme.Modules.pullback (sliceAt f (⟨(Scheme.TwoAffineOpenCover.specMap Γ(A, V) B) ≫ hV.fromSpec, rfl⟩ : SchemeHomOver (((Scheme.TwoAffineOpenCover.specMap Γ(A, V) B) ≫ hV.fromSpec) ≫ f) f))).obj F)).H0
          (𝒦.comap (pullback.fst f (((Scheme.TwoAffineOpenCover.specMap Γ(A, V) B) ≫ hV.fromSpec) ≫ f))) ≃ₗ[B]
        (OModulePresheaf.ofModules (pullback.snd (pullback.snd f (hV.fromSpec ≫ f)) (Scheme.TwoAffineOpenCover.specMap Γ(A, V) B))
          ((Scheme.Modules.pullback (pullback.fst (pullback.snd f (hV.fromSpec ≫ f)) (Scheme.TwoAffineOpenCover.specMap Γ(A, V) B))).obj
            ((Scheme.Modules.pullback (sliceAt f (⟨hV.fromSpec, rfl⟩ : SchemeHomOver (hV.fromSpec ≫ f) f))).obj F))).H0
          ((𝒦.comap (pullback.fst f (hV.fromSpec ≫ f))).baseChange (pullback.snd f (hV.fromSpec ≫ f)) B)) ∧
      ∀ i : ℕ, Nonempty ((OModulePresheaf.ofModules q ((Scheme.Modules.pullback (sliceAt f (⟨(Scheme.TwoAffineOpenCover.specMap Γ(A, V) B) ≫ hV.fromSpec, rfl⟩ : SchemeHomOver (((Scheme.TwoAffineOpenCover.specMap Γ(A, V) B) ≫ hV.fromSpec) ≫ f) f))).obj F)).HSucc
          (𝒦.comap (pullback.fst f (((Scheme.TwoAffineOpenCover.specMap Γ(A, V) B) ≫ hV.fromSpec) ≫ f))) i ≃ₗ[B]
        (OModulePresheaf.ofModules (pullback.snd (pullback.snd f (hV.fromSpec ≫ f)) (Scheme.TwoAffineOpenCover.specMap Γ(A, V) B))
          ((Scheme.Modules.pullback (pullback.fst (pullback.snd f (hV.fromSpec ≫ f)) (Scheme.TwoAffineOpenCover.specMap Γ(A, V) B))).obj
            ((Scheme.Modules.pullback (sliceAt f (⟨hV.fromSpec, rfl⟩ : SchemeHomOver (hV.fromSpec ≫ f) f))).obj F))).HSucc
          ((𝒦.comap (pullback.fst f (hV.fromSpec ≫ f))).baseChange (pullback.snd f (hV.fromSpec ≫ f)) B) i) := by
    intro q hq
    subst hq
    exact AlgebraicGeometry.OModulePresheaf.nonempty_cechEquiv_ofModules_of_iso_pullback_of_isIso
      (pullback.snd (pullback.snd f (hV.fromSpec ≫ f)) (Scheme.TwoAffineOpenCover.specMap Γ(A, V) B)) Φ _ hN' _ e _ _
  exact key _ hΦsnd.symm

end S_AlgebraicGeometry_Polarisation_nonempty_cechEquiv_sliceAt_comap_baseChange_of_isAffineOpen
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_nonempty_cechEquiv_sliceAt_comap_baseChange_of_isAffineOpen (solution)
