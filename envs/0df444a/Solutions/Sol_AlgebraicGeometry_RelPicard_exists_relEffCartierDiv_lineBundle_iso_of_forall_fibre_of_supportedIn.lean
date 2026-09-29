-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_relEffCartierDiv_lineBundle_iso_of_forall_fibre_of_supportedIn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/ec21db91-95a2-574a-94f9-707142caa2cf

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_one_iff_isInvertible
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal_of_supportedIn
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_comap_zeroSchemeIdeal
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_field
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isIso_ev_app_tensorUnit
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullbackSection_transposeSection_eq_zero_iff
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_zeroSchemeIdeal_comp_eq_of_isIso
import Theorems.Thm_AlgebraicGeometry_RelPicard_relEffCartierDiv_I_eq_of_lineBundle_iso_tensor_pullback_of_supportedIn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_relEffCartierDiv_lineBundle_iso_of_forall_fibre_of_supportedIn
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd"
p2m_attr_erase "simp" "AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_relEffCartierDiv_lineBundle_iso_of_forall_fibre_of_supportedIn.AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra"

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "IsLocallyNoetherian SmoothOfRelativeDimension Scheme.Modules.pushforward IsProper Scheme.Modules.pullback LocallyOfFiniteType.isLocallyNoetherian Scheme.Hom LocallyOfFiniteType Spec Scheme Flat Scheme.Modules.pullbackCongr Scheme.fromSpecResidueField_apply Scheme.Modules.pullbackPushforwardAdjunction Scheme.Modules Scheme.Hom.comp_apply Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible Scheme.Modules.dual RelEffCartierDiv mapOnProdOver mapOnProdOver_snd isPullback_mapOnProdOver Scheme.Modules.zeroSchemeIdeal Scheme.Modules.pullbackSection Scheme.Modules.IsLocallyFreeOfRank Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal_of_supportedIn Scheme.Modules.IsInvertible.pullback_dual Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field Scheme.Modules.IsInvertible.isIso_ev_app_tensorUnit Scheme.Modules.IsInvertible.pullbackSection_transposeSection_eq_zero_iff Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso" namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "fromSpecResidueField ringCatSheaf Modules.pushforward Modules.pullback Hom Γ empty Modules.pullbackCongr fromSpecResidueField_apply Modules.pullbackPushforwardAdjunction Modules Opens Hom.comp_apply PresheafOfModules Modules.pullbackComp Modules.IsInvertible Modules.dual TwoAffineOpenCover Modules.zeroSchemeIdeal Modules.pullbackSection Modules.IsLocallyFreeOfRank Modules.isLocallyFreeOfRank_one_iff_isInvertible Modules.IsInvertible.pullback_dual Modules.IsInvertible.nonempty_iso_tensorUnit_of_field Modules.IsInvertible.isIso_ev_app_tensorUnit Modules.IsInvertible.pullbackSection_transposeSection_eq_zero_iff Modules.zeroSchemeIdeal_comp_eq_of_isIso" namespace Modules p2m_export "AlgebraicGeometry.Scheme.Modules" "hom_ext pushforward pullback Hom pullbackCongr pullbackPushforwardAdjunction pullbackComp IsInvertible tensor dual zeroSchemeIdeal pullbackSection IsLocallyFreeOfRank isLocallyFreeOfRank_one_iff_isInvertible IsInvertible.pullback_dual IsInvertible.nonempty_iso_tensorUnit_of_field IsInvertible.isIso_ev_app_tensorUnit IsInvertible.pullbackSection_transposeSection_eq_zero_iff zeroSchemeIdeal_comp_eq_of_isIso" end AlgebraicGeometry.Scheme.Modules
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules" in

theorem AlgebraicGeometry.Scheme.Modules.hom_eq_zero_of_isEmpty {Y : Scheme.{u}} [IsEmpty ↥Y]
    {A B : Y.Modules} (f : A ⟶ B) : f = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  have hU : U.unop = ⊥ := le_bot_iff.mp fun y _ => isEmptyElim y
  have hsub : Subsingleton Γ(Y, U.unop) :=
    CommRingCat.subsingleton_of_isTerminal (Y.sheaf.isTerminalOfEqEmpty hU)
  haveI : Subsingleton (Y.ringCatSheaf.val.obj U) := hsub
  haveI : Subsingleton (B.val.obj U) := Module.subsingleton (Y.ringCatSheaf.val.obj U) _
  ext m
  exact Subsingleton.elim _ _

open Opposite in
set_option maxHeartbeats 6400000 in
theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [Flat c]
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)] (g : ℕ)

    (hpush : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
      (F : (pullback c t).Modules), Scheme.Modules.IsInvertible F → ∀ (n : ℕ),
      (∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T) (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F)).H1 ∧
          Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F)).H0 = n) →
      Scheme.Modules.IsLocallyFreeOfRank n ((Scheme.Modules.pushforward (pullback.snd c t)).obj F))

    (hcounit : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
      (F : (pullback c t).Modules), Scheme.Modules.IsInvertible F →
      (∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T) (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F)).H1 ∧
          Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F)).H0 = 1) →
      ∀ {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ T),
        (Scheme.Modules.pullback (mapOnProdOver c x rfl)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction (pullback.snd c t)).counit.app F) ≠ 0)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (M : (pullback c t).Modules) (hM : Scheme.Modules.IsInvertible M)
    (hfib : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H0 = 1)

    (hZfib : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ T)
      (σ : 𝟙_ (pullback c (x ≫ t)).Modules ⟶ (Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj M), σ ≠ 0 →
      ∃ Dx : RelEffCartierDiv c g (x ≫ t), Dx.I = Scheme.Modules.zeroSchemeIdeal σ ∧ Dx.SupportedIn U) :
    ∃ (D : RelEffCartierDiv c g t) (N : T.Modules), Scheme.Modules.IsInvertible N ∧
      Nonempty (D.lineBundle ≅ M ⊗ (Scheme.Modules.pullback (pullback.snd c t)).obj N) ∧
      ∀ (d' : ℕ) (D' : RelEffCartierDiv c d' t) (N' : T.Modules), Scheme.Modules.IsInvertible N' → D'.SupportedIn U →
        Nonempty (D'.lineBundle ≅ M ⊗ (Scheme.Modules.pullback (pullback.snd c t)).obj N') → D'.I = D.I := by
  classical

  have hP1 := hpush t M hM 1 hfib
  set q := pullback.snd c t with hq
  set P := (Scheme.Modules.pushforward q).obj M with hPdef
  have hP : Scheme.Modules.IsInvertible P := (Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible P).mp hP1
  set X := (Scheme.Modules.pullback q).obj P with hXdef
  have hX : Scheme.Modules.IsInvertible X := hP.pullback q

  set φ : X ⟶ M := (Scheme.Modules.pullbackPushforwardAdjunction q).counit.app M with hφ
  have hev := Scheme.Modules.IsInvertible.isIso_ev_app_tensorUnit hX
  obtain ⟨s, hs⟩ : ∃ s : 𝟙_ (pullback c t).Modules ⟶ M ⊗ Scheme.Modules.dual X,
      (ihom.ev X).app (𝟙_ (pullback c t).Modules) ≫ s = φ ▷ Scheme.Modules.dual X :=
    ⟨CategoryTheory.inv ((ihom.ev X).app (𝟙_ (pullback c t).Modules)) (I := hev) ≫ φ ▷ Scheme.Modules.dual X,
      @IsIso.hom_inv_id_assoc _ _ _ _ _ hev _ _⟩

  have hNZ : ∀ (k : Type u) [Field k] (x : Spec (CommRingCat.of k) ⟶ T),
      Scheme.Modules.pullbackSection (mapOnProdOver c x rfl) s ≠ 0 := by
    intro k _ x h0
    exact hcounit t M hM hfib x
      ((Scheme.Modules.IsInvertible.pullbackSection_transposeSection_eq_zero_iff
        (mapOnProdOver c x rfl) hX φ s hs).mp h0)

  haveI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian t
  have hMX : Scheme.Modules.IsInvertible (M ⊗ Scheme.Modules.dual X) := hM.tensor hX.dual.1
  obtain ⟨ePd⟩ := Scheme.Modules.IsInvertible.pullback_dual q hP
  obtain ⟨D, hDI, hDU, ⟨eD, heD⟩⟩ := RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal_of_supportedIn (f := c) U (g := t) hMX s g (by
    intro k _ _ x

    have hcart : IsPullback (mapOnProdOver c x rfl) (pullback.snd c (x ≫ t)) q x :=
      isPullback_mapOnProdOver c x rfl
    set g' := mapOnProdOver c x rfl with hg'

    have hPx : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback x).obj (Scheme.Modules.dual P)) :=
      hP.dual.1.pullback x
    obtain ⟨eNk⟩ := Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field k _ hPx
    have hcomp : g' ≫ q = pullback.snd c (x ≫ t) ≫ x := hcart.w
    let eDX : (Scheme.Modules.pullback g').obj (Scheme.Modules.dual X) ≅ 𝟙_ (pullback c (x ≫ t)).Modules :=
      (Scheme.Modules.pullback g').mapIso ePd.symm ≪≫
        ((Scheme.Modules.pullbackComp g' q).app (Scheme.Modules.dual P)) ≪≫
        ((Scheme.Modules.pullbackCongr hcomp).app (Scheme.Modules.dual P)) ≪≫
        ((Scheme.Modules.pullbackComp (pullback.snd c (x ≫ t)) x).app (Scheme.Modules.dual P)).symm ≪≫
        (Scheme.Modules.pullback (pullback.snd c (x ≫ t))).mapIso eNk ≪≫
        (Functor.Monoidal.εIso (Scheme.Modules.pullback (pullback.snd c (x ≫ t)))).symm
    let eF : (Scheme.Modules.pullback g').obj (M ⊗ Scheme.Modules.dual X) ≅ (Scheme.Modules.pullback g').obj M :=
      (Functor.Monoidal.μIso (Scheme.Modules.pullback g') M (Scheme.Modules.dual X)).symm ≪≫
        whiskerLeftIso _ eDX ≪≫ ρ_ _

    set σ := Scheme.Modules.pullbackSection g' s ≫ eF.hom with hσ
    have hσ0 : σ ≠ 0 := by
      intro h0
      apply hNZ k x
      have : Scheme.Modules.pullbackSection g' s = σ ≫ eF.inv := by rw [hσ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
      rw [this, h0, Limits.zero_comp]
    obtain ⟨Dx, hDx, hDxU⟩ := hZfib k x σ hσ0
    refine ⟨Dx, ?_, hDxU⟩
    rw [hMX.comap_zeroSchemeIdeal g' s, hDx, hσ, Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso])

  have hne : ∀ x : T, ∃ y : ↥(pullback c t), (pullback.snd c t).base y = x := by
    intro x
    by_contra hx
    push_neg at hx
    have hE : IsEmpty ↥(pullback c (T.fromSpecResidueField x ≫ t)) := ⟨fun y' =>
      hx ((mapOnProdOver c (T.fromSpecResidueField x) (rfl : T.fromSpecResidueField x ≫ t = _)).base y') (by
        rw [← Scheme.Hom.comp_apply, mapOnProdOver_snd c (T.fromSpecResidueField x) (rfl : T.fromSpecResidueField x ≫ t = _),
          Scheme.Hom.comp_apply]
        exact Scheme.fromSpecResidueField_apply x _)⟩
    exact hcounit t M hM hfib (T.fromSpecResidueField x) (@Scheme.Modules.hom_eq_zero_of_isEmpty _ hE _ _ _)

  refine ⟨D, Scheme.Modules.dual P, hP.dual.1, ⟨eD.symm ≪≫ (whiskerLeftIso M ePd.symm)⟩, ?_⟩
  intro d' D' N' hN' hD'U hiso
  exact relEffCartierDiv_I_eq_of_lineBundle_iso_tensor_pullback_of_supportedIn R c U hpush t M hM hfib hne
    D' D hD'U hDU N' (Scheme.Modules.dual P) hN' hP.dual.1 hiso.some (eD.symm ≪≫ (whiskerLeftIso M ePd.symm))

end S_AlgebraicGeometry_RelPicard_exists_relEffCartierDiv_lineBundle_iso_of_forall_fibre_of_supportedIn
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_exists_relEffCartierDiv_lineBundle_iso_of_forall_fibre_of_supportedIn (solution)
