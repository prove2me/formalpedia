-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.RepresentsRelSubPic.postComp_transport_comp_fst_eq_comp_transport_of_baseChangeIso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/23c02277-3514-594f-81f5-5f6024eeb8f9

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JOnePGeom
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_pullback_rigidify_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_fst_rigidify_iso_of_isInvertible
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JOnePOpsV2
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_postComp_transport_comp_fst_eq_comp_transport_of_baseChangeIso
p2m_attr_erase "instance" "SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve"

universe u

theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {D : RelativePic0Designation R c} (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (R' : Type u) [CommRing R'] [Algebra R R']
    (hR : RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
      (algEquivZeroCut (baseChange R c R') (sectionBaseChange R' ε)) (D.baseChange R'))
    (hPR : Nonempty (hR.poincare.L ≅ (BaseChange.ofR c ε R'
      (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩)).L))
    (W : C ≅ C) (hW : W.hom ≫ c = c) (hW' : W.inv ≫ c = c)
    (W' : pullback c (specMap R R') ≅ pullback c (specMap R R'))
    (hW'₁ : W'.hom ≫ pullback.fst c (specMap R R') = pullback.fst c (specMap R R') ≫ W.hom)
    (hW'₂ : W'.hom ≫ baseChange R c R' = baseChange R c R') (hW'₂' : W'.inv ≫ baseChange R c R' = baseChange R c R')
    (θ : SchemeHomOver D.toBase D.toBase)
    (hθ : (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (M : RigidifiedLineBundle c ε t) (hM : FibrewiseAlgEquivZero M)
        (N : RigidifiedLineBundle c ε t) (hN : FibrewiseAlgEquivZero N)
        (Q : T.Modules), Scheme.Modules.IsInvertible Q →
        Nonempty (N.L ≅ (Scheme.Modules.pullback (curveChange (c := c) (c' := c) W.inv hW' t)).obj M.L ⊗
          (Scheme.Modules.pullback (pullback.snd c t)).obj Q) →
        postComp θ (h.classify t M hM) = h.classify t N hN))
    (θ' : SchemeHomOver (D.baseChange R').toBase (D.baseChange R').toBase)
    (hθ' : (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R'))
        (M : RigidifiedLineBundle (baseChange R c R') (sectionBaseChange R' ε) t) (hM : FibrewiseAlgEquivZero M)
        (N : RigidifiedLineBundle (baseChange R c R') (sectionBaseChange R' ε) t) (hN : FibrewiseAlgEquivZero N)
        (Q : T.Modules), Scheme.Modules.IsInvertible Q →
        Nonempty (N.L ≅ (Scheme.Modules.pullback (curveChange (c := baseChange R c R') (c' := baseChange R c R') W'.inv hW'₂' t)).obj M.L ⊗
          (Scheme.Modules.pullback (pullback.snd (baseChange R c R') t)).obj Q) →
        postComp θ' (hR.classify t M hM) = hR.classify t N hN)) :
    ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) (v : SchemeHomOver t (D.baseChange R').toBase),
      (postComp θ' v).1 ≫ pullback.fst D.toBase (specMap R R') = (v.1 ≫ pullback.fst D.toBase (specMap R R')) ≫ θ.1 := by
  classical
  intro T t v

  let P := h.poincare
  let Pb := hR.poincare
  let Db := D.baseChange R'
  let u : Db.P ⟶ Spec (CommRingCat.of R) := Db.toBase ≫ specMap R R'
  let fstD : SchemeHomOver u D.toBase := ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩
  let cW : ∀ {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of R)), pullback c s ⟶ pullback c s :=
    fun s => curveChange (c := c) (c' := c) W.inv hW' s
  let cW' : ∀ {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of R')),
      pullback (baseChange R c R') s ⟶ pullback (baseChange R c R') s :=
    fun s => curveChange (c := baseChange R c R') (c' := baseChange R c R') W'.inv hW'₂' s

  suffices key : θ'.1 ≫ pullback.fst D.toBase (specMap R R') = pullback.fst D.toBase (specMap R R') ≫ θ.1 by
    show (v.1 ≫ θ'.1) ≫ _ = _
    rw [Category.assoc, key, Category.assoc]

  have CUT : ∀ {C₀ : Scheme.{u}} {R₀ : Type u} [CommRing R₀]
      {cc : C₀ ⟶ Spec (CommRingCat.of R₀)} {ε₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R₀))) cc}
      (g : C₀ ⟶ C₀) (hg : g ≫ cc = cc) {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of R₀))
      (M : RigidifiedLineBundle cc ε₀ s), FibrewiseAlgEquivZero M →
      FibrewiseAlgEquivZero (RigidifiedLineBundle.ofInvertible (ε := ε₀)
        ((Scheme.Modules.pullback (curveChange (c := cc) (c' := cc) g hg s)).obj M.L) (M.isInvertible.pullback _)) := by
    intro C₀ R₀ _ cc ε₀ g hg S s M hM k _ _ x
    obtain ⟨e49⟩ := AlgebraicGeometry.Scheme.Modules.nonempty_pullback_fst_rigidify_iso_of_isInvertible
      (rigSection cc s ε₀) (pullback.snd cc s) ((Scheme.Modules.pullback (curveChange (c := cc) (c' := cc) g hg s)).obj M.L)
      (M.isInvertible.pullback _) k x
    rw [RigidifiedLineBundle.ofInvertible_L]
    refine IsAlgEquivZero.of_iso e49.symm ?_

    let e : Limits.pullback (pullback.snd cc s) x ⟶ Limits.pullback (pullback.snd cc s) x :=
      pullback.map _ _ _ _ (curveChange (c := cc) (c' := cc) g hg s) (𝟙 _) (𝟙 _)
        (by rw [Category.comp_id, curveChange_snd]) (by simp)
    have he : e ≫ fibreAt cc s x = fibreAt cc s x := by
      simp only [e, fibreAt, pullback.lift_snd, Category.comp_id]
    have hfst : e ≫ pullback.fst (pullback.snd cc s) x = pullback.fst (pullback.snd cc s) x ≫ curveChange (c := cc) (c' := cc) g hg s := by
      simp only [e, pullback.lift_fst]
    refine IsAlgEquivZero.of_iso ?_ ((hM k x).pullback e he)
    exact (Scheme.Modules.pullbackComp _ _).app M.L ≪≫ (Scheme.Modules.pullbackCongr hfst).app M.L ≪≫
      ((Scheme.Modules.pullbackComp _ _).app M.L).symm

  have IDpt : ∀ {C₀ : Scheme.{u}} {R₀ : Type u} [CommRing R₀] {cc : C₀ ⟶ Spec (CommRingCat.of R₀)}
      {ε₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R₀))) cc} {D₀ : RelativePic0Designation R₀ cc}
      (h₀ : RepresentsRelSubPic cc ε₀ (algEquivZeroCut cc ε₀) D₀),
      Nonempty ((h₀.poincare.pullbackAlong (⟨𝟙 D₀.P, Category.id_comp _⟩ : SchemeHomOver D₀.toBase D₀.toBase)).L ≅ h₀.poincare.L) := by
    intro C₀ R₀ _ cc ε₀ D₀ h₀
    have hb : baseChangeSnd cc (⟨𝟙 D₀.P, Category.id_comp _⟩ : SchemeHomOver D₀.toBase D₀.toBase) = 𝟙 _ := by
      apply pullback.hom_ext
      · rw [BaseChange.baseChangeSnd_fst', Category.id_comp]
      · rw [BaseChange.baseChangeSnd_snd', Category.id_comp]; exact (Category.comp_id _).symm
    exact ⟨(Scheme.Modules.pullbackCongr hb).app _ ≪≫ (Scheme.Modules.pullbackId _).app _⟩

  let N₀ := RigidifiedLineBundle.ofInvertible (ε := ε) ((Scheme.Modules.pullback (cW D.toBase)).obj P.L) (P.isInvertible.pullback _)
  have hN₀ : FibrewiseAlgEquivZero N₀ := CUT W.inv hW' D.toBase P h.poincare_mem
  have Iθ : Nonempty ((P.pullbackAlong θ).L ≅ N₀.L) := by
    have hid : (⟨𝟙 D.P, Category.id_comp _⟩ : SchemeHomOver D.toBase D.toBase) = h.classify D.toBase P h.poincare_mem :=
      h.classify_unique _ _ _ _ (IDpt h)
    have hcl : postComp θ (h.classify D.toBase P h.poincare_mem) = h.classify D.toBase N₀ hN₀ :=
      hθ D.toBase P h.poincare_mem N₀ hN₀ (rigCorrection ε D.toBase ((Scheme.Modules.pullback (cW D.toBase)).obj P.L))
        (((P.isInvertible.pullback _).pullback _).dual).1 ⟨Iso.refl _⟩
    have hθeq : postComp θ (h.classify D.toBase P h.poincare_mem) = θ := by
      rw [← hid]; exact Subtype.ext (Category.id_comp _)
    rw [hθeq] at hcl
    rw [hcl]
    exact h.classify_spec D.toBase N₀ hN₀

  let N₀' := RigidifiedLineBundle.ofInvertible (ε := sectionBaseChange R' ε)
    ((Scheme.Modules.pullback (cW' Db.toBase)).obj Pb.L) (Pb.isInvertible.pullback _)
  have hN₀' : FibrewiseAlgEquivZero N₀' := CUT W'.inv hW'₂' Db.toBase Pb hR.poincare_mem
  have Iθ' : Nonempty ((Pb.pullbackAlong θ').L ≅ N₀'.L) := by
    have hid : (⟨𝟙 Db.P, Category.id_comp _⟩ : SchemeHomOver Db.toBase Db.toBase) = hR.classify Db.toBase Pb hR.poincare_mem :=
      hR.classify_unique _ _ _ _ (IDpt hR)
    have hcl : postComp θ' (hR.classify Db.toBase Pb hR.poincare_mem) = hR.classify Db.toBase N₀' hN₀' :=
      hθ' Db.toBase Pb hR.poincare_mem N₀' hN₀' (rigCorrection (sectionBaseChange R' ε) Db.toBase ((Scheme.Modules.pullback (cW' Db.toBase)).obj Pb.L))
        (((Pb.isInvertible.pullback _).pullback _).dual).1 ⟨Iso.refl _⟩
    have hθeq : postComp θ' (hR.classify Db.toBase Pb hR.poincare_mem) = θ' := by
      rw [← hid]; exact Subtype.ext (Category.id_comp _)
    rw [hθeq] at hcl
    rw [hcl]
    exact hR.classify_spec Db.toBase N₀' hN₀'

  let g₁ : SchemeHomOver u D.toBase := postComp fstD (BaseChange.overR R' θ')
  let g₂ : SchemeHomOver u D.toBase := postComp θ fstD

  let X := P.pullbackAlong fstD

  have hcWnat : ∀ {S S' : Scheme.{u}} {s : S ⟶ Spec (CommRingCat.of R)} {s' : S' ⟶ Spec (CommRingCat.of R)}
      (ψ : SchemeHomOver s' s), baseChangeSnd c ψ ≫ cW s = cW s' ≫ baseChangeSnd c ψ := by
    intro S S' s s' ψ
    apply pullback.hom_ext
    · simp only [Category.assoc, cW, curveChange, pullback.lift_fst, BaseChange.baseChangeSnd_fst']
      rw [← Category.assoc, BaseChange.baseChangeSnd_fst']
    · simp only [Category.assoc, cW, curveChange, pullback.lift_snd, BaseChange.baseChangeSnd_snd', Category.comp_id]
      rw [← Category.assoc, pullback.lift_snd, Category.comp_id]

  have I₂ : Nonempty ((P.pullbackAlong g₂).L ≅
      (RigidifiedLineBundle.ofInvertible (ε := ε) ((Scheme.Modules.pullback (cW u)).obj X.L) (X.isInvertible.pullback _)).L) := by
    obtain ⟨iθ⟩ := Iθ
    obtain ⟨inat⟩ := RigidifiedLineBundle.nonempty_ofInvertible_pullbackAlong_iso (ε := ε) fstD
      (L := (Scheme.Modules.pullback (cW D.toBase)).obj P.L) (P.isInvertible.pullback _)

    have isq : (Scheme.Modules.pullback (baseChangeSnd c fstD)).obj ((Scheme.Modules.pullback (cW D.toBase)).obj P.L) ≅
        (Scheme.Modules.pullback (cW u)).obj X.L :=
      (Scheme.Modules.pullbackComp _ _).app P.L ≪≫ (Scheme.Modules.pullbackCongr (hcWnat fstD)).app P.L ≪≫
        ((Scheme.Modules.pullbackComp _ _).app P.L).symm
    obtain ⟨icongr⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso (ε := ε)
      ((P.isInvertible.pullback _).pullback _) (X.isInvertible.pullback _) isq
    exact ⟨(RigidifiedLineBundle.pullbackAlongPullbackAlongIso' P θ fstD).symm ≪≫
      (Scheme.Modules.pullback (baseChangeSnd c fstD)).mapIso iθ ≪≫ inat ≪≫ icongr⟩

  have I₁ : Nonempty ((P.pullbackAlong g₁).L ≅
      (RigidifiedLineBundle.ofInvertible (ε := ε) ((Scheme.Modules.pullback (cW u)).obj X.L) (X.isInvertible.pullback _)).L) := by
    obtain ⟨iθ'⟩ := Iθ'
    obtain ⟨ePR⟩ := hPR

    have iX : (BaseChange.toR c ε R' Pb).L ≅ X.L :=
      (Scheme.Modules.pullback (BaseChange.κ c R' Db.toBase).inv).mapIso ePR ≪≫ BaseChange.toR_ofR_iso c ε R' X

    have i1 : ((BaseChange.toR c ε R' Pb).pullbackAlong (BaseChange.overR R' θ')).L ≅
        (Scheme.Modules.pullback (BaseChange.κ c R' Db.toBase).inv).obj N₀'.L :=
      BaseChange.toR_pullbackAlong_iso c ε R' θ' Pb ≪≫ (Scheme.Modules.pullback (BaseChange.κ c R' Db.toBase).inv).mapIso iθ'

    obtain ⟨i2⟩ := AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_pullback_rigidify_iso
      (σ := rigSection (baseChange R c R') Db.toBase (sectionBaseChange R' ε)) (q := pullback.snd (baseChange R c R') Db.toBase)
      (σ' := rigSection c u ε) (q' := pullback.snd c u)
      (𝟙 Db.P) (BaseChange.κ c R' Db.toBase).inv
      (by rw [Category.id_comp]; exact BaseChange.rigSection_κ_inv c ε R' Db.toBase)
      (by rw [Category.comp_id, ← BaseChange.κ_hom_snd c R' Db.toBase, ← Category.assoc, Iso.inv_hom_id, Category.id_comp])
      (L := (Scheme.Modules.pullback (cW' Db.toBase)).obj Pb.L) (Pb.isInvertible.pullback _)

    have hW'inv : W'.inv ≫ pullback.fst c (specMap R R') = pullback.fst c (specMap R R') ≫ W.inv := by
      rw [Iso.inv_comp_eq, ← Category.assoc, hW'₁, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have hκinv_fst : (BaseChange.κ c R' Db.toBase).inv ≫ pullback.fst (baseChange R c R') Db.toBase ≫ pullback.fst c (specMap R R') =
        pullback.fst c u := by
      rw [← BaseChange.κ_hom_fst, Iso.inv_hom_id_assoc]
    have hκinv_snd : (BaseChange.κ c R' Db.toBase).inv ≫ pullback.snd (baseChange R c R') Db.toBase = pullback.snd c u := by
      rw [← BaseChange.κ_hom_snd, Iso.inv_hom_id_assoc]
    have hcW'fst : cW' Db.toBase ≫ pullback.fst (baseChange R c R') Db.toBase = pullback.fst (baseChange R c R') Db.toBase ≫ W'.inv :=
      pullback.lift_fst _ _ _
    have hcW'snd : cW' Db.toBase ≫ pullback.snd (baseChange R c R') Db.toBase = pullback.snd (baseChange R c R') Db.toBase :=
      curveChange_snd _ _ _
    have hcWfst : cW u ≫ pullback.fst c u = pullback.fst c u ≫ W.inv := pullback.lift_fst _ _ _
    have hcWsnd : cW u ≫ pullback.snd c u = pullback.snd c u := curveChange_snd _ _ _
    have hκW0 : (BaseChange.κ c R' Db.toBase).inv ≫ cW' Db.toBase ≫ (BaseChange.κ c R' Db.toBase).hom = cW u := by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, BaseChange.κ_hom_fst, ← Category.assoc (cW' Db.toBase), hcW'fst,
          Category.assoc, hW'inv, ← Category.assoc, ← Category.assoc, hcWfst]
        congr 1
      · rw [Category.assoc, Category.assoc, BaseChange.κ_hom_snd, hcW'snd, hκinv_snd, hcWsnd]
    have hκW : (BaseChange.κ c R' Db.toBase).inv ≫ cW' Db.toBase = cW u ≫ (BaseChange.κ c R' Db.toBase).inv := by
      rw [← hκW0, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have i3 : (Scheme.Modules.pullback (BaseChange.κ c R' Db.toBase).inv).obj ((Scheme.Modules.pullback (cW' Db.toBase)).obj Pb.L) ≅
        (Scheme.Modules.pullback (cW u)).obj X.L :=
      (Scheme.Modules.pullbackComp _ _).app Pb.L ≪≫ (Scheme.Modules.pullbackCongr hκW).app Pb.L ≪≫
        ((Scheme.Modules.pullbackComp _ _).app Pb.L).symm ≪≫ (Scheme.Modules.pullback (cW u)).mapIso iX
    obtain ⟨i4⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso (ε := ε)
      ((Pb.isInvertible.pullback _).pullback _) (X.isInvertible.pullback _) i3

    have i0 : (P.pullbackAlong g₁).L ≅ ((BaseChange.toR c ε R' Pb).pullbackAlong (BaseChange.overR R' θ')).L :=
      (RigidifiedLineBundle.pullbackAlongPullbackAlongIso' P fstD (BaseChange.overR R' θ')).symm ≪≫
        (Scheme.Modules.pullback (baseChangeSnd c (BaseChange.overR R' θ'))).mapIso iX.symm
    refine ⟨i0 ≪≫ i1 ≪≫ ?_ ≪≫ i4⟩
    rw [RigidifiedLineBundle.ofInvertible_L, RigidifiedLineBundle.ofInvertible_L]
    exact i2

  obtain ⟨e₁⟩ := I₁
  obtain ⟨e₂⟩ := I₂
  have hg : g₁ = g₂ := h.ext_of_iso u g₁ g₂ ⟨e₁ ≪≫ e₂.symm⟩
  exact congrArg Subtype.val hg

end S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_postComp_transport_comp_fst_eq_comp_transport_of_baseChangeIso
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_postComp_transport_comp_fst_eq_comp_transport_of_baseChangeIso (solution)
