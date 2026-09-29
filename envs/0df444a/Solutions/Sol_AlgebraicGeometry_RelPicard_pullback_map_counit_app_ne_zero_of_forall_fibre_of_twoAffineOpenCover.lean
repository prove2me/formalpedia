-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.pullback_map_counit_app_ne_zero_of_forall_fibre_of_twoAffineOpenCover
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/3719692e-9561-56e3-9e40-57ba6ebea81f

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_ModulesBaseChangeHom
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_AlgebraicGeometry_RelPicard_isIso_baseChangeHom_pushforward_of_forall_fibre_of_twoAffineOpenCover
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_H0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_pullback_map_counit_app_ne_zero_of_forall_fibre_of_twoAffineOpenCover
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_pullback_map_counit_app_ne_zero_of_forall_fibre_of_twoAffineOpenCover.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_pullback_map_counit_app_ne_zero_of_forall_fibre_of_twoAffineOpenCover.AlgebraicGeometry.RelPicard NeronModelInfra CategoryTheory.MonoidalCategory AlgebraicGeometry.SmoothProperCurve"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_preimage Scheme.Modules.Hom.zero_app Scheme.Modules.pushforward IsProper Scheme.Modules.pullback Scheme.Modules.Hom LocallyOfFiniteType Spec Spec.map Scheme Scheme.Modules.Hom.app Flat Spec.preimage Scheme.Modules.pullbackPushforwardAdjunction Scheme.Modules Scheme.Modules.IsInvertible mapOnProdOver isPullback_mapOnProdOver RelPicard.BaseChange.baseChangeSnd_snd' Scheme.Modules.pullbackTwoSquare Scheme.Modules.baseChangeHom Scheme.Modules.baseChangeHom_counit RelPicard.isIso_baseChangeHom_pushforward_of_forall_fibre_of_twoAffineOpenCover RelPicard.exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd fibreAt fibreModule BaseChange.baseChangeSnd_snd' isIso_baseChangeHom_pushforward_of_forall_fibre_of_twoAffineOpenCover exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback"
namespace NZCounitSol
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

variable {Y S : Scheme.{u}} (π : Y ⟶ S)

theorem app_top_eq_zero_of_counit_eq_zero (N : Y.Modules)
    (h : (Scheme.Modules.pullbackPushforwardAdjunction π).counit.app N = 0) (m : Γ(N, ⊤)) : m = 0 := by
  have tri := (Scheme.Modules.pullbackPushforwardAdjunction π).right_triangle_components N

  have e1 := congrArg (fun φ => Scheme.Modules.Hom.app φ ⊤ (show Γ((Scheme.Modules.pushforward π).obj N, ⊤) from m)) tri

  change (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction π).counit.app N) (π ⁻¹ᵁ ⊤))
      ((Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction π).unit.app _) ⊤)
        (show Γ((Scheme.Modules.pushforward π).obj N, ⊤) from m))
    = (show Γ((Scheme.Modules.pushforward π).obj N, ⊤) from m) at e1
  have e3 := congrArg (fun φ => Scheme.Modules.Hom.app φ (π ⁻¹ᵁ ⊤)
    ((Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction π).unit.app _) ⊤)
      (show Γ((Scheme.Modules.pushforward π).obj N, ⊤) from m))) h

  simp only [Scheme.Modules.Hom.zero_app] at e3
  have e4 : (show Γ((Scheme.Modules.pushforward π).obj N, ⊤) from m) = 0 :=
    e1.symm.trans (e3.trans (by
      first
        | rfl
        | (rw [Scheme.Modules.Hom.zero_app]; rfl)
        | simp [Scheme.Modules.Hom.zero_app]
        | exact map_zero _))
  exact e4

end AlgebraicGeometry.RelPicard.NZCounitSol

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_preimage Scheme.Modules.Hom.zero_app Scheme.Modules.pushforward IsProper Scheme.Modules.pullback Scheme.Modules.Hom LocallyOfFiniteType Spec Spec.map Scheme Scheme.Modules.Hom.app Flat Spec.preimage Scheme.Modules.pullbackPushforwardAdjunction Scheme.Modules Scheme.Modules.IsInvertible mapOnProdOver isPullback_mapOnProdOver RelPicard.BaseChange.baseChangeSnd_snd' Scheme.Modules.pullbackTwoSquare Scheme.Modules.baseChangeHom Scheme.Modules.baseChangeHom_counit RelPicard.isIso_baseChangeHom_pushforward_of_forall_fibre_of_twoAffineOpenCover RelPicard.exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd fibreAt fibreModule BaseChange.baseChangeSnd_snd' isIso_baseChangeHom_pushforward_of_forall_fibre_of_twoAffineOpenCover exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback"
namespace NZCounitSol'
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"
open AlgebraicGeometry.RelPicard.NZCounitSol

theorem main
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [Flat c] (𝒱 : C.TwoAffineOpenCover)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (M : (pullback c t).Modules) (hM : Scheme.Modules.IsInvertible M)
    (hfib : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H0 = 1)
    {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ T) :
    (Scheme.Modules.pullback (mapOnProdOver c x rfl)).map
      ((Scheme.Modules.pullbackPushforwardAdjunction (pullback.snd c t)).counit.app M) ≠ 0 := by
  intro h0

  haveI hbc := AlgebraicGeometry.RelPicard.isIso_baseChangeHom_pushforward_of_forall_fibre_of_twoAffineOpenCover R c 𝒱
    (⟨x, rfl⟩ : SchemeHomOver (x ≫ t) t) M hM 1 hfib

  have key := Scheme.Modules.baseChangeHom_counit (π := pullback.snd c t) (ψ := x) (π' := pullback.snd c (x ≫ t))
    (g' := baseChangeSnd c (⟨x, rfl⟩ : SchemeHomOver (x ≫ t) t))
    (RelPicard.BaseChange.baseChangeSnd_snd' (cc := c) (ψ := (⟨x, rfl⟩ : SchemeHomOver (x ≫ t) t))) M
  have h0' : (Scheme.Modules.pullback (baseChangeSnd c (⟨x, rfl⟩ : SchemeHomOver (x ≫ t) t))).map
      ((Scheme.Modules.pullbackPushforwardAdjunction (pullback.snd c t)).counit.app M) = 0 := h0
  have key2 : (Scheme.Modules.pullback (pullback.snd c (x ≫ t))).map
        (Scheme.Modules.baseChangeHom
          (RelPicard.BaseChange.baseChangeSnd_snd' (cc := c) (ψ := (⟨x, rfl⟩ : SchemeHomOver (x ≫ t) t))) M) ≫
      (Scheme.Modules.pullbackPushforwardAdjunction (pullback.snd c (x ≫ t))).counit.app
        ((Scheme.Modules.pullback (baseChangeSnd c (⟨x, rfl⟩ : SchemeHomOver (x ≫ t) t))).obj M) = 0 := by
    refine key.trans ?_
    refine (congrArg (fun φ => (Scheme.Modules.pullbackTwoSquare
      (RelPicard.BaseChange.baseChangeSnd_snd' (cc := c) (ψ := (⟨x, rfl⟩ : SchemeHomOver (x ≫ t) t)))).natTrans.app
        ((Scheme.Modules.pushforward (pullback.snd c t)).obj M) ≫ φ) h0').trans ?_
    exact Limits.comp_zero
  have hcounit : (Scheme.Modules.pullbackPushforwardAdjunction (pullback.snd c (x ≫ t))).counit.app
      ((Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj M) = 0 := by
    have := (cancel_epi ((Scheme.Modules.pullback (pullback.snd c (x ≫ t))).map
      (Scheme.Modules.baseChangeHom
        (RelPicard.BaseChange.baseChangeSnd_snd' (cc := c) (ψ := (⟨x, rfl⟩ : SchemeHomOver (x ≫ t) t))) M))).mp
      (key2.trans (Limits.comp_zero).symm)
    exact this

  have hsec : ∀ m : Γ((Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj M, ⊤), m = 0 :=
    app_top_eq_zero_of_counit_eq_zero (pullback.snd c (x ≫ t)) _ hcounit

  letI : Algebra R k := (Spec.preimage (x ≫ t)).hom.toAlgebra
  have hx : Spec.map (CommRingCat.ofHom (algebraMap R k)) = x ≫ t := by
    change Spec.map (CommRingCat.ofHom (Spec.preimage (x ≫ t)).hom) = _
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  let 𝒱k : (pullback c (x ≫ t)).TwoAffineOpenCover := hx ▸ 𝒱.pullback c k

  obtain ⟨𝒲, ⟨e0⟩, -⟩ := RelPicard.exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback c t M x
    (pullback.snd c (x ≫ t)) (mapOnProdOver c x rfl) (isPullback_mapOnProdOver c x rfl)
    ((Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj M) (Iso.refl _) 𝒱k
  obtain ⟨-, h1⟩ := hfib k x 𝒲
  have hrank : Module.finrank k (𝒱k.sectionsOf (pullback.snd c (x ≫ t))
      ((Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj M)).H0 = 1 := e0.finrank_eq.trans h1

  obtain ⟨eΓ, -⟩ := 𝒱k.exists_linearEquiv_sectionsOf_H0 (pullback.snd c (x ≫ t))
    ((Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj M)
  haveI : Nontrivial (𝒱k.sectionsOf (pullback.snd c (x ≫ t))
      ((Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj M)).H0 := Module.nontrivial_of_finrank_eq_succ hrank
  obtain ⟨a, b, hab⟩ := exists_pair_ne (𝒱k.sectionsOf (pullback.snd c (x ≫ t))
      ((Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj M)).H0
  apply hab
  rw [← eΓ.apply_symm_apply a, ← eΓ.apply_symm_apply b, hsec (eΓ.symm a), hsec (eΓ.symm b)]

end AlgebraicGeometry.RelPicard.NZCounitSol'

end

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [Flat c] (𝒱 : C.TwoAffineOpenCover)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (M : (pullback c t).Modules) (hM : Scheme.Modules.IsInvertible M)
    (hfib : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H0 = 1)
    {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ T) :
    (Scheme.Modules.pullback (mapOnProdOver c x rfl)).map
      ((Scheme.Modules.pullbackPushforwardAdjunction (pullback.snd c t)).counit.app M) ≠ 0 :=
  AlgebraicGeometry.RelPicard.NZCounitSol'.main R c 𝒱 t M hM hfib x

end S_AlgebraicGeometry_RelPicard_pullback_map_counit_app_ne_zero_of_forall_fibre_of_twoAffineOpenCover
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_pullback_map_counit_app_ne_zero_of_forall_fibre_of_twoAffineOpenCover (solution)
