-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.subsingleton_sections_of_inPicZero_of_not_iso_unit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/25c421fe-8876-59a5-b04e-eee93a0962d3

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_pullback_negMor_iso_dual_of_inPicZero
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_forall_app_eq_smul
import Theorems.Thm_AlgebraicGeometry_geometricallyIrreducible_iff_bijective_appTop_of_isProper_of_smooth
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_Hom_mono_iff_injective
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_hom_eq_zero_of_pullback_map_eq_zero_of_isIntegral
import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_subsingleton_sections_of_inPicZero_of_not_iso_unit
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq"
p2m_attr_erase "simp" "ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

namespace PosHelpers

open Opposite

theorem exists_unit_hom_ne_zero_of_section {X : Scheme.{0}} (M : X.Modules) (s : Γ(M, ⊤)) (hs : s ≠ 0) :
    ∃ φ : 𝟙_ X.Modules ⟶ M, φ ≠ 0 := by
  let σ : M.val.sections := PresheafOfModules.sectionsMk
    (fun U => M.presheaf.map (homOfLE (le_top (a := U.unop))).op s)
    (fun U V g => by
      show M.presheaf.map g (M.presheaf.map (homOfLE (le_top (a := U.unop))).op s) =
        M.presheaf.map (homOfLE (le_top (a := V.unop))).op s
      rw [← CategoryTheory.comp_apply, ← M.presheaf.map_comp]
      congr 1)
  refine ⟨M.unitHomEquiv.symm σ, fun h => hs ?_⟩
  have h1 := SheafOfModules.unitHomEquiv_apply_coe M (M.unitHomEquiv.symm σ) (op ⊤)
  rw [Equiv.apply_symm_apply, h] at h1

  have h2 : σ.val (op ⊤) = s := by
    show M.presheaf.map (homOfLE (le_top (a := (⊤ : X.Opens)))).op s = s
    rw [show (homOfLE (le_top (a := (⊤ : X.Opens)))).op = 𝟙 (op ⊤) from Subsingleton.elim _ _, M.presheaf.map_id]
    rfl
  rw [← h2, h1]
  show ((0 : 𝟙_ X.Modules ⟶ M).app ⊤) (1 : Γ(X, ⊤)) = 0
  rw [Scheme.Modules.Hom.zero_app]
  rfl

theorem app_top_one_ne_zero {X : Scheme.{0}} {M : X.Modules} (φ : 𝟙_ X.Modules ⟶ M) (hφ : φ ≠ 0) :
    (φ.app ⊤) (1 : Γ(X, ⊤)) ≠ 0 := by
  intro h
  apply hφ
  apply M.unitHomEquiv.injective
  apply PresheafOfModules.sections_ext
  intro U
  rw [SheafOfModules.unitHomEquiv_apply_coe, SheafOfModules.unitHomEquiv_apply_coe]
  have hU : (1 : X.ringCatSheaf.val.obj U) =
      (SheafOfModules.unit X.ringCatSheaf).val.map (homOfLE (le_top (a := U.unop))).op (1 : X.ringCatSheaf.val.obj (op ⊤)) :=
    (PresheafOfModules.unit_map_one _ (homOfLE (le_top (a := U.unop))).op).symm
  have h' : (φ.val.app (op ⊤)) (1 : X.ringCatSheaf.val.obj (op ⊤)) = 0 := h
  have h'' : ((0 : 𝟙_ X.Modules ⟶ M).val.app (op ⊤)) (1 : X.ringCatSheaf.val.obj (op ⊤)) = 0 := by
    show ((0 : 𝟙_ X.Modules ⟶ M).app ⊤) _ = 0
    rw [Scheme.Modules.Hom.zero_app]; rfl
  rw [hU, PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply]
  exact congrArg (fun y => (M.val.map (homOfLE (le_top (a := U.unop))).op) y) (h'.trans h''.symm)

theorem negMor_comp_negMor {k : Type} [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f) :
    negMor f L ≫ negMor f L = 𝟙 A := by
  letI := L.pointGroup f
  have hN : negMor f L ≫ f = f := negMor_over f L

  have hnat : GoodReductionJacobian.schemeHomOverComp (negMor f L) hN (L.inv f (idPt f)) =
      L.inv f (GoodReductionJacobian.schemeHomOverComp (negMor f L) hN (idPt f)) := by
    have h : GoodReductionJacobian.schemeHomOverComp (negMor f L) hN (L.inv f (idPt f)) *
        GoodReductionJacobian.schemeHomOverComp (negMor f L) hN (idPt f) = 1 := by
      show L.mul f _ _ = L.one f
      rw [← L.mul_natural f f (negMor f L) hN, L.inv_mul_cancel, L.one_natural f f (negMor f L) hN]
    exact (inv_eq_of_mul_eq_one_left h).symm
  have hid : GoodReductionJacobian.schemeHomOverComp (negMor f L) hN (idPt f) = L.inv f (idPt f) := by
    apply Subtype.ext; show negMor f L ≫ 𝟙 A = negMor f L; rw [Category.comp_id]
  rw [hid] at hnat
  have h2 : L.inv f (L.inv f (idPt f)) = idPt f := by
    show (idPt f)⁻¹⁻¹ = idPt f
    exact inv_inv _
  rw [h2] at hnat
  have h3 := congrArg Subtype.val hnat
  exact h3

end PosHelpers

namespace AlphaHelpers

open Opposite

theorem app_eq_zero_of_le {X : Scheme} {𝓛 : X.Modules} (s : 𝟙_ X.Modules ⟶ 𝓛) {U V : X.Opens} (hVU : V ≤ U)
    (r : Γ(X, U)) (hsr : s.app U r = 0) (hunit : IsUnit (X.presheaf.map (homOfLE hVU).op r)) : s.app V = 0 := by

  have h1 : (s.app V) (1 : Γ(X, V)) = 𝓛.presheaf.map (homOfLE hVU).op ((s.app U) (1 : Γ(X, U))) := by
    have hn := PresheafOfModules.naturality_apply s.val (homOfLE hVU).op (1 : Γ(X, U))
    have h1' : (𝟙_ X.Modules).val.map (homOfLE hVU).op (1 : Γ(X, U)) = (1 : Γ(X, V)) :=
      PresheafOfModules.unit_map_one _ _
    rw [h1'] at hn
    exact hn
  have hr1 : (s.app U) r = r • (s.app U) (1 : Γ(X, U)) := by
    rw [← Scheme.Modules.Hom.app_smul]
    exact congrArg (s.app U) (mul_one r).symm
  have h2 : X.presheaf.map (homOfLE hVU).op r • (s.app V) (1 : Γ(X, V)) = 0 := by
    rw [h1]
    show X.presheaf.map (homOfLE hVU).op r • 𝓛.presheaf.map (homOfLE hVU).op ((s.app U) (1 : Γ(X, U))) = 0
    rw [← Scheme.Modules.map_smul, ← hr1, hsr, map_zero]
  have h3 : (s.app V) (1 : Γ(X, V)) = 0 := by
    obtain ⟨w, hw⟩ := hunit
    rw [← hw] at h2
    have := congrArg (fun m => (↑w⁻¹ : Γ(X, V)) • m) h2
    simpa [← mul_smul, smul_zero] using this
  have key : ∀ y : Γ(X, V), (s.app V) y = 0 := by
    intro y
    have : (s.app V) y = y • (s.app V) (1 : Γ(X, V)) := by
      rw [← Scheme.Modules.Hom.app_smul]
      exact congrArg (s.app V) (mul_one y).symm
    rw [this, h3, smul_zero]
  ext y
  exact key y

theorem mono_of_ne_zero {X : Scheme} [IsIntegral X] {𝓛 : X.Modules} (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (s : 𝟙_ X.Modules ⟶ 𝓛) (hs : s ≠ 0) : Mono s := by
  rw [Scheme.Modules.Hom.mono_iff_injective]
  intro U
  show ∀ a b : Γ(X, U), s.app U a = s.app U b → a = b
  intro a b hab
  by_contra hne
  apply hs
  have hr : a - b ≠ 0 := sub_ne_zero.mpr hne
  have hsr : s.app U (a - b) = 0 := by
    have h := map_sub (ConcreteCategory.hom (s.app U)) a b
    exact h.trans (sub_eq_zero.mpr hab)

  have hUne : (U : Set X).Nonempty := by
    by_contra hU
    apply hr
    have hU' : U = ⊥ := TopologicalSpace.Opens.coe_eq_empty.mp (Set.not_nonempty_iff_eq_empty.mp hU)
    have : Subsingleton Γ(X, U) := by
      rw [hU']; exact CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEmpty)
    exact Subsingleton.elim _ _

  let D : X.Opens := X.basicOpen (a - b)
  have hξU : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hUne)
  have hξD : genericPoint X ∈ D := by
    rw [Scheme.mem_basicOpen _ _ _ hξU]
    have hne0 : (X.presheaf.germ U (genericPoint X) hξU) (a - b) ≠ 0 := by
      intro h0
      apply hr
      apply germ_injective_of_isIntegral X (genericPoint X) hξU
      rw [h0]
      exact (map_zero _).symm
    exact isUnit_iff_ne_zero.mpr hne0
  have hDne : (D : Set X).Nonempty := ⟨_, hξD⟩

  have hD : ∀ W : (D : Scheme).Opens, s.app (D.ι ''ᵁ W) = 0 := by
    intro W
    have hWD : D.ι ''ᵁ W ≤ D := by
      intro x hx
      obtain ⟨y, -, rfl⟩ := hx
      exact y.2
    have hWU : D.ι ''ᵁ W ≤ U := hWD.trans (X.basicOpen_le _)
    refine app_eq_zero_of_le s hWU (a - b) hsr ?_
    have hu : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le (a - b))).op (a - b)) := RingedSpace.isUnit_res_basicOpen _ (a - b)
    have := hu.map (X.presheaf.map (homOfLE hWD).op).hom
    rwa [← CategoryTheory.comp_apply, ← X.presheaf.map_comp] at this
  have hD' : (Scheme.Modules.restrictFunctor D.ι).map s = 0 := by
    apply Scheme.Modules.hom_ext
    intro W
    rw [Scheme.Modules.Hom.zero_app]
    exact hD W
  have hD'' : (Scheme.Modules.pullback D.ι).map s = 0 := by
    let e := Scheme.Modules.restrictFunctorIsoPullback D.ι
    have hn := e.hom.naturality s

    rw [hD', zero_comp] at hn
    rw [← cancel_epi (e.hom.app _), ← hn, comp_zero]
  exact Scheme.Modules.IsInvertible.hom_eq_zero_of_pullback_map_eq_zero_of_isIntegral (Scheme.Modules.isInvertible_unit X) h𝓛 s D hDne hD''

end AlphaHelpers

namespace GammaCoh

theorem comp_iso_ne_zero {C : Type*} [Category C] [HasZeroMorphisms C] {U F G : C} {s : U ⟶ F} (hs : s ≠ 0)
    (e : F ≅ G) : s ≫ e.hom ≠ 0 := by
  intro h
  apply hs
  have : s = (s ≫ e.hom) ≫ e.inv := by simp
  rw [this, h, zero_comp]

theorem exists_ne_zero_pullback_of_isIso {X X' : Scheme.{0}} (ψ : X ⟶ X') [IsIso ψ] (𝓕 : X'.Modules)
    (s : 𝟙_ X'.Modules ⟶ 𝓕) (hs : s ≠ 0) :
    ∃ t : 𝟙_ X.Modules ⟶ (Scheme.Modules.pullback ψ).obj 𝓕, t ≠ 0 := by
  refine ⟨(Scheme.Modules.pullbackTensorUnitObjIso ψ).inv ≫ (Scheme.Modules.pullback ψ).map s, ?_⟩
  intro h
  apply hs
  have h1 : (Scheme.Modules.pullback ψ).map s = 0 := by
    have : (Scheme.Modules.pullback ψ).map s =
        (Scheme.Modules.pullbackTensorUnitObjIso ψ).hom ≫
          ((Scheme.Modules.pullbackTensorUnitObjIso ψ).inv ≫ (Scheme.Modules.pullback ψ).map s) := by simp
    rw [this, h, comp_zero]

  let E : Scheme.Modules.pullback ψ ⋙ Scheme.Modules.pullback (inv ψ) ≅ 𝟭 X'.Modules :=
    Scheme.Modules.pullbackComp (inv ψ) ψ ≪≫ Scheme.Modules.pullbackCongr (IsIso.inv_hom_id ψ) ≪≫
      Scheme.Modules.pullbackId X'
  have h2 : (Scheme.Modules.pullback ψ ⋙ Scheme.Modules.pullback (inv ψ)).map s = 0 := by
    show (Scheme.Modules.pullback (inv ψ)).map ((Scheme.Modules.pullback ψ).map s) = 0
    rw [h1, Functor.map_zero]
  have h3 := E.hom.naturality s
  rw [h2, zero_comp, Functor.id_map] at h3
  have h4 : E.hom.app _ ≫ s = 0 := h3.symm
  have : s = E.inv.app _ ≫ (E.hom.app _ ≫ s) := by
    rw [← Category.assoc, ← NatTrans.comp_app, E.inv_hom_id, NatTrans.id_app, Category.id_comp]
  rw [this]
  exact (congrArg (fun x => E.inv.app _ ≫ x) h4).trans comp_zero

end GammaCoh

theorem solution
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (M : A.Modules) (hM : InPicZero f L M) (hM1 : ¬ Nonempty (M ≅ 𝟙_ (A.Modules))) :
    Subsingleton (Γ(M, ⊤) : Type) := by

  haveI : IsProper f := hA.proper
  haveI : Smooth f := hA.smooth
  haveI hGI : GeometricallyIntegral f := hA.geometricallyIntegral
  haveI : IsIntegral A := GeometricallyIntegral.isIntegral_of_subsingleton f
  haveI : IsIso (negMor f L) := ⟨⟨negMor f L, PosHelpers.negMor_comp_negMor f L, PosHelpers.negMor_comp_negMor f L⟩⟩
  have hMi : Scheme.Modules.IsInvertible M := hM.1

  by_contra hns
  apply hM1
  rw [not_subsingleton_iff_nontrivial] at hns
  obtain ⟨m, hm⟩ := exists_ne (0 : Γ(M, ⊤))
  obtain ⟨s, hs⟩ := PosHelpers.exists_unit_hom_ne_zero_of_section M m hm
  haveI : Mono s := AlphaHelpers.mono_of_ne_zero hMi s hs

  obtain ⟨eN⟩ := nonempty_pullback_negMor_iso_dual_of_inPicZero k f L hc hA M hM
  obtain ⟨s', hs'⟩ := GammaCoh.exists_ne_zero_pullback_of_isIso (negMor f L) M s hs
  have ht' : s' ≫ eN.hom ≠ 0 := GammaCoh.comp_iso_ne_zero hs' eN
  obtain ⟨hd, ⟨eM⟩⟩ := Scheme.Modules.IsInvertible.dual_monoidalV2 hMi

  let e' : Scheme.Modules.dual M ⊗ M ≅ 𝟙_ A.Modules := β_ _ _ ≪≫ eM
  let tl : ∀ {P Q : A.Modules} (i : P ≅ Q), tensorLeft P ≅ tensorLeft Q := fun i =>
    NatIso.ofComponents (fun Z => whiskerRightIso i Z) (fun f => by simp [whisker_exchange])
  let E : A.Modules ≌ A.Modules := CategoryTheory.Equivalence.mk (tensorLeft M) (tensorLeft (Scheme.Modules.dual M))
    ((leftUnitorNatIso A.Modules).symm ≪≫ tl e'.symm ≪≫ tensorLeftTensor _ _)
    ((tensorLeftTensor _ _).symm ≪≫ tl eM ≪≫ leftUnitorNatIso A.Modules)
  haveI : (tensorLeft M).Faithful := (inferInstance : E.functor.Faithful)
  let t : M ⟶ 𝟙_ A.Modules := (ρ_ M).inv ≫ (M ◁ (s' ≫ eN.hom)) ≫ eM.hom
  have ht : t ≠ 0 := by
    intro h0
    apply ht'
    apply (tensorLeft M).map_injective
    rw [Functor.map_zero]
    show M ◁ (s' ≫ eN.hom) = 0
    have : M ◁ (s' ≫ eN.hom) = (ρ_ M).hom ≫ t ≫ eM.inv := by simp [t]
    rw [this, h0, Limits.zero_comp, Limits.comp_zero]

  have hγ : t ≫ s ≠ 0 := by
    intro h0; apply ht; rw [← cancel_mono s, h0, Limits.zero_comp]
  obtain ⟨u, hu⟩ := Scheme.Modules.IsInvertible.exists_forall_app_eq_smul hMi (t ≫ s)
  have hu0 : u ≠ 0 := by
    intro h0; apply hγ
    apply Scheme.Modules.hom_ext; intro U; ext y
    rw [Scheme.Modules.Hom.zero_app, hu U y, h0, map_zero, zero_smul]; rfl
  have hbij := (geometricallyIrreducible_iff_bijective_appTop_of_isProper_of_smooth f).mp inferInstance
  have huU : IsUnit u := by
    obtain ⟨c, hc'⟩ := hbij.2 u
    have hc0 : c ≠ 0 := by rintro rfl; apply hu0; rw [← hc', map_zero]
    rw [← hc']
    exact (IsUnit.mk0 c hc0).map _
  obtain ⟨w, hw⟩ := huU
  haveI : IsIso (t ≫ s) := by
    rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
    intro U
    rw [ConcreteCategory.isIso_iff_bijective]
    constructor
    · intro a b hab
      rw [hu U a, hu U b, ← hw] at hab
      have := congrArg (fun z => A.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (↑w⁻¹ : Γ(A, ⊤)) • z) hab
      simpa [← mul_smul, ← map_mul] using this
    · intro b
      refine ⟨A.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (↑w⁻¹ : Γ(A, ⊤)) • b, ?_⟩
      rw [hu U, ← hw, ← mul_smul, ← map_mul, Units.mul_inv, map_one, one_smul]
  haveI : IsSplitEpi s := IsSplitEpi.mk' ⟨inv (t ≫ s) ≫ t, by rw [Category.assoc, IsIso.inv_hom_id]⟩
  haveI : IsIso s := isIso_of_mono_of_isSplitEpi s
  exact ⟨(asIso s).symm⟩

end S_AlgebraicGeometry_Polarisation_subsingleton_sections_of_inPicZero_of_not_iso_unit
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_subsingleton_sections_of_inPicZero_of_not_iso_unit (solution)
