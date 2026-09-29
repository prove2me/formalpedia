-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_restrictHom_pair_of_twoGluedSmoothCurves
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/c9af9cd9-c59d-53a1-95ac-83820027506f

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_isLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_restrictHom_pair_of_twoGluedSmoothCurves
p2m_attr_erase "instance" "SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply"
set_option autoImplicit false
set_option linter.unusedVariables false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard

namespace S1A

p2m_open "CategoryTheory.MonoidalCategory"

section General

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
  {P : SubPicGroupCondition c ε} {D : RelativePic0Designation R c}

theorem nonempty_pullbackAlong_mul_iso (h : RepresentsRelSubPic c ε P.toSubPicCondition D)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a b : SchemeHomOver t D.toBase) :
    Nonempty ((h.poincare.pullbackAlong (h.relativeGroupLaw.mul t a b)).L ≅
      ((h.poincare.pullbackAlong a).tensor (h.poincare.pullbackAlong b)).L) := by
  letI := h.grpObj
  letI := P.commGroupObj (Opposite.op (Over.mk t))
  have hm := h.homEquiv_mul (Over.mk t) (schemeHomOverToOverHom a) (schemeHomOverToOverHom b)
  have hv := congrArg Subtype.val hm
  exact Quotient.exact hv

theorem eq_classify_pullbackAlong (h : RepresentsRelSubPic c ε P.toSubPicCondition D)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t D.toBase) :
    a = h.classify t (h.poincare.pullbackAlong a) (P.pullback_mem _ _ a _ h.poincare_mem) :=
  h.classify_unique t _ _ a ⟨Iso.refl _⟩

variable {C' : Scheme.{u}} {c' : C' ⟶ Spec (CommRingCat.of R)} {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c'}
  {P' : SubPicGroupCondition c' ε'} {D' : RelativePic0Designation R c'}

theorem hom_of_classifies (h : RepresentsRelSubPic c ε P.toSubPicCondition D)
    (h' : RepresentsRelSubPic c' ε' P'.toSubPicCondition D') (ν : SchemeHomOver D.toBase D'.toBase)
    (F : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}, RigidifiedLineBundle c ε t → RigidifiedLineBundle c' ε' t)
    (hFcongr : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (M N : RigidifiedLineBundle c ε t),
      Nonempty (M.L ≅ N.L) → Nonempty ((F M).L ≅ (F N).L))
    (hFtensor : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (M N : RigidifiedLineBundle c ε t),
      Nonempty ((F (M.tensor N)).L ≅ ((F M).tensor (F N)).L))
    (hν : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (a : SchemeHomOver t D.toBase),
      Nonempty ((h'.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a ν)).L ≅ (F (h.poincare.pullbackAlong a)).L))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a b : SchemeHomOver t D.toBase) :
    NeronModelInfra.schemeHomOverComp (h.relativeGroupLaw.mul t a b) ν =
      h'.relativeGroupLaw.mul t (NeronModelInfra.schemeHomOverComp a ν) (NeronModelInfra.schemeHomOverComp b ν) := by
  apply h'.ext_of_iso t
  obtain ⟨e₁⟩ := hν (h.relativeGroupLaw.mul t a b)
  obtain ⟨e₂⟩ := hFcongr _ _ (nonempty_pullbackAlong_mul_iso h t a b)
  obtain ⟨e₃⟩ := hFtensor (h.poincare.pullbackAlong a) (h.poincare.pullbackAlong b)
  obtain ⟨e₄⟩ := (RigidifiedLineBundle.tensor_congr (Nonempty.intro (hν a).some.symm) (Nonempty.intro (hν b).some.symm) :
    Nonempty (((F (h.poincare.pullbackAlong a)).tensor (F (h.poincare.pullbackAlong b))).L ≅ _))
  obtain ⟨e₅⟩ := nonempty_pullbackAlong_mul_iso h' t (NeronModelInfra.schemeHomOverComp a ν)
    (NeronModelInfra.schemeHomOverComp b ν)
  exact ⟨e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄ ≪≫ e₅.symm⟩

theorem nonempty_pullbackCurve_tensor_iso (f : C' ⟶ C) (hf : f ≫ c = c') (hε : ε'.1 ≫ f = ε.1)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (M N : RigidifiedLineBundle c ε t) :
    Nonempty (((M.tensor N).pullbackCurve f hf hε).L ≅ ((M.pullbackCurve f hf hε).tensor (N.pullbackCurve f hf hε)).L) :=
  ⟨Scheme.Modules.pullbackTensorObjIso _ _ _⟩

theorem nonempty_ofInvertible_pullback_tensor_iso (f : C' ⟶ C) (hf : f ≫ c = c')
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (M N : RigidifiedLineBundle c ε t) :
    Nonempty ((RigidifiedLineBundle.ofInvertible (ε := ε')
        ((Scheme.Modules.pullback (curveChange f hf t)).obj (M.tensor N).L)
        ((M.tensor N).isInvertible.pullback _)).L ≅
      ((RigidifiedLineBundle.ofInvertible (ε := ε') ((Scheme.Modules.pullback (curveChange f hf t)).obj M.L)
          (M.isInvertible.pullback _)).tensor
        (RigidifiedLineBundle.ofInvertible (ε := ε') ((Scheme.Modules.pullback (curveChange f hf t)).obj N.L)
          (N.isInvertible.pullback _))).L) := by
  obtain ⟨e₁⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso (ε := ε')
    ((M.tensor N).isInvertible.pullback (curveChange f hf t))
    ((M.isInvertible.pullback (curveChange f hf t)).tensor (N.isInvertible.pullback (curveChange f hf t)))
    (Scheme.Modules.pullbackTensorObjIso _ _ _)
  obtain ⟨e₂⟩ := RigidifiedLineBundle.nonempty_ofInvertible_tensor_iso (ε := ε')
    (M.isInvertible.pullback (curveChange f hf t)) (N.isInvertible.pullback (curveChange f hf t))
  exact ⟨e₁ ≪≫ e₂⟩

theorem nonempty_pullback_iso_unit_of_field {K : Type u} [Field K] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (CommRingCat.of K)) {N : (Spec (CommRingCat.of K)).Modules} (hN : Scheme.Modules.IsInvertible N) :
    Nonempty ((Scheme.Modules.pullback g).obj N ≅ 𝟙_ Y.Modules) := by
  obtain ⟨e⟩ := hN.nonempty_iso_tensorUnit_of_isLocalRing
  exact ⟨(Scheme.Modules.pullback g).mapIso e ≪≫ Scheme.Modules.pullbackTensorUnitObjIso g⟩

theorem fibrewiseAlgEquivZero_ofInvertible_pullback (f : C' ⟶ C) (hf : f ≫ c = c')
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {M : RigidifiedLineBundle c ε t} (hM : FibrewiseAlgEquivZero M) :
    FibrewiseAlgEquivZero (RigidifiedLineBundle.ofInvertible (ε := ε')
      ((Scheme.Modules.pullback (curveChange f hf t)).obj M.L) (M.isInvertible.pullback _)) := by
  intro K _ _ s
  have hL := M.isInvertible.pullback (curveChange f hf t)

  let e : Limits.pullback (pullback.snd c' t) s ⟶ Limits.pullback (pullback.snd c t) s :=
    pullback.map _ _ _ _ (curveChange f hf t) (𝟙 _) (𝟙 T)
      (by rw [Category.comp_id, curveChange_snd]) (by simp)
  have he : e ≫ fibreAt c t s = fibreAt c' t s := by
    simp only [e, fibreAt, pullback.lift_snd, Category.comp_id]
  have hfst : e ≫ pullback.fst (pullback.snd c t) s =
      pullback.fst (pullback.snd c' t) s ≫ curveChange f hf t := by
    simp only [e, pullback.lift_fst]
  have h1 : IsAlgEquivZero (fibreAt c' t s)
      ((Scheme.Modules.pullback (pullback.fst (pullback.snd c' t) s)).obj
        ((Scheme.Modules.pullback (curveChange f hf t)).obj M.L)) := by
    refine IsAlgEquivZero.of_iso ?_ ((hM K s).pullback e he)
    exact (Scheme.Modules.pullbackComp _ _).app M.L ≪≫
      (Scheme.Modules.pullbackCongr hfst).app M.L ≪≫
      ((Scheme.Modules.pullbackComp _ _).app M.L).symm

  have hN : Scheme.Modules.IsInvertible (rigCorrection ε' t ((Scheme.Modules.pullback (curveChange f hf t)).obj M.L)) :=
    ((hL.pullback _).dual).1
  obtain ⟨u⟩ := nonempty_pullback_iso_unit_of_field (fibreAt c' t s) (hN.pullback s)
  have ecorr : (Scheme.Modules.pullback (pullback.fst (pullback.snd c' t) s)).obj
      ((Scheme.Modules.pullback (pullback.snd c' t)).obj
        (rigCorrection ε' t ((Scheme.Modules.pullback (curveChange f hf t)).obj M.L))) ≅ 𝟙_ _ :=
    (Scheme.Modules.pullbackComp _ _).app _ ≪≫
      (Scheme.Modules.pullbackCongr (pullback.condition)).app _ ≪≫
      ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫ u

  refine IsAlgEquivZero.of_iso ?_ h1
  rw [RigidifiedLineBundle.ofInvertible_L_eq_tensor]
  exact (ρ_ _).symm ≪≫ (Iso.refl _ ⊗ᵢ ecorr.symm) ≪≫ (Scheme.Modules.pullbackTensorObjIso _ _ _).symm

end General

end S1A

open S1A _root_.CategoryTheory.MonoidalCategory in
theorem solution
    {k : Type u} [Field k] [IsAlgClosed k]
    {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) [IsProper x] (hXred : IsReduced X)
    (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hjs : ∀ z : X, z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hcr : IsReduced (pullback i₁.1 i₂.1)) (s : ℕ) (hs : Nat.card ↥(pullback i₁.1 i₂.1) = s) (hs0 : 0 < s)
    (ε : SchemeHomOver (𝟙 _) x) (ε₁ : SchemeHomOver (𝟙 _) c₁) (hε : ε₁.1 ≫ i₁.1 = ε.1)
    (ε₂ : SchemeHomOver (𝟙 _) c₂)
    (D : RelativePic0Designation k x) (hD : RepresentsRelSubPic x ε (algEquivZeroCut x ε) D)
    (D₁ : RelativePic0Designation k c₁) (hD₁ : RepresentsRelSubPic c₁ ε₁ (algEquivZeroCut c₁ ε₁) D₁)
    (D₂ : RelativePic0Designation k c₂) (hD₂ : RepresentsRelSubPic c₂ ε₂ (algEquivZeroCut c₂ ε₂) D₂) :
    ∃ (ν₁ : SchemeHomOver D.toBase D₁.toBase) (ν₂ : SchemeHomOver D.toBase D₂.toBase),
      ν₁ = RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε hD hD₁ ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (a : SchemeHomOver t D.toBase),
        Nonempty ((hD₂.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a ν₂)).L ≅
          Scheme.Modules.rigidify (rigSection c₂ t ε₂) (pullback.snd c₂ t)
            ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 t)).obj (hD.poincare.pullbackAlong a).L))) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (a b : SchemeHomOver t D.toBase),
        NeronModelInfra.schemeHomOverComp
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut x ε) hD).mul t a b) ν₁ =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₁ ε₁) hD₁).mul t
            (NeronModelInfra.schemeHomOverComp a ν₁) (NeronModelInfra.schemeHomOverComp b ν₁)) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (a b : SchemeHomOver t D.toBase),
        NeronModelInfra.schemeHomOverComp
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut x ε) hD).mul t a b) ν₂ =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₂ ε₂) hD₂).mul t
            (NeronModelInfra.schemeHomOverComp a ν₂) (NeronModelInfra.schemeHomOverComp b ν₂)) := by

  have hcut₂ := fibrewiseAlgEquivZero_ofInvertible_pullback (ε' := ε₂) i₂.1 i₂.2 (M := hD.poincare) hD.poincare_mem
  let ν₂ : SchemeHomOver D.toBase D₂.toBase := hD₂.classify D.toBase _ hcut₂
  refine ⟨RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε hD hD₁, ν₂, rfl, ?_, ?_, ?_⟩
  ·
    intro T t a
    obtain ⟨e₁⟩ := hD₂.classify_spec D.toBase _ hcut₂
    obtain ⟨e₂⟩ := RigidifiedLineBundle.nonempty_ofInvertible_pullbackAlong_iso (ε := ε₂) a
      (hD.poincare.isInvertible.pullback (curveChange i₂.1 i₂.2 D.toBase))
    refine ⟨(hD₂.poincare.pullbackAlongPullbackAlongIso' ν₂ a).symm ≪≫
      (Scheme.Modules.pullback _).mapIso e₁ ≪≫ e₂ ≪≫ Scheme.Modules.rigidifyMapIso _ _ ?_⟩
    exact (Scheme.Modules.pullbackComp _ _).app _ ≪≫
      (Scheme.Modules.pullbackCongr (curveChange_baseChangeSnd i₂.1 i₂.2 a).symm).app _ ≪≫
      ((Scheme.Modules.pullbackComp _ _).app _).symm
  ·
    intro T t a b
    refine hom_of_classifies (P := algEquivZeroGroupCut x ε) (P' := algEquivZeroGroupCut c₁ ε₁) hD hD₁ _
      (fun M => M.pullbackCurve i₁.1 i₁.2 hε)
      (fun M N hMN => RigidifiedLineBundle.pullbackCurve_congr i₁.1 i₁.2 hε hMN)
      (fun M N => nonempty_pullbackCurve_tensor_iso i₁.1 i₁.2 hε M N) ?_ t a b
    intro T t a
    have hpc := RepresentsRelSubPic.postComp_pullbackHom_classify i₁.1 i₁.2 hε hD hD₁ t (hD.poincare.pullbackAlong a)
      ((algEquivZeroCut x ε).pullback_mem _ _ a _ hD.poincare_mem)
    have ha : a = hD.classify t (hD.poincare.pullbackAlong a)
        ((algEquivZeroCut x ε).pullback_mem _ _ a _ hD.poincare_mem) := hD.classify_unique t _ _ a ⟨Iso.refl _⟩
    rw [← ha] at hpc
    change Nonempty ((hD₁.poincare.pullbackAlong (postComp _ a)).L ≅ _)
    rw [hpc]
    exact hD₁.classify_spec t _ _
  ·
    intro T t a b
    refine hom_of_classifies (P := algEquivZeroGroupCut x ε) (P' := algEquivZeroGroupCut c₂ ε₂) hD hD₂ ν₂
      (fun M => RigidifiedLineBundle.ofInvertible (ε := ε₂)
        ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 _)).obj M.L) (M.isInvertible.pullback _))
      (fun M N hMN => RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso (ε := ε₂) _ _
        ((Scheme.Modules.pullback _).mapIso hMN.some))
      (fun M N => nonempty_ofInvertible_pullback_tensor_iso (ε := ε) (ε' := ε₂) i₂.1 i₂.2 M N) ?_ t a b
    intro T t a
    obtain ⟨e₁⟩ := hD₂.classify_spec D.toBase _ hcut₂
    obtain ⟨e₂⟩ := RigidifiedLineBundle.nonempty_ofInvertible_pullbackAlong_iso (ε := ε₂) a
      (hD.poincare.isInvertible.pullback (curveChange i₂.1 i₂.2 D.toBase))
    obtain ⟨e₃⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso (ε := ε₂)
      ((hD.poincare.isInvertible.pullback (curveChange i₂.1 i₂.2 D.toBase)).pullback (baseChangeSnd c₂ a))
      ((hD.poincare.pullbackAlong a).isInvertible.pullback (curveChange i₂.1 i₂.2 t))
      ((Scheme.Modules.pullbackComp _ _).app _ ≪≫
        (Scheme.Modules.pullbackCongr (curveChange_baseChangeSnd i₂.1 i₂.2 a).symm).app _ ≪≫
        ((Scheme.Modules.pullbackComp _ _).app _).symm)
    exact ⟨(hD₂.poincare.pullbackAlongPullbackAlongIso' ν₂ a).symm ≪≫ (Scheme.Modules.pullback _).mapIso e₁ ≪≫ e₂ ≪≫ e₃⟩

end S_AlgebraicGeometry_RelPicard_exists_restrictHom_pair_of_twoGluedSmoothCurves
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_exists_restrictHom_pair_of_twoGluedSmoothCurves (solution)
