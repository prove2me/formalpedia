-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.RepresentsRelSubPic.postComp_transport_eq_self_of_ker_restrictPair_of_iso_comp_eq_of_crossing_of_twoGluedSmoothCurves
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/f152fdd5-465a-55e3-8560-33f3fc914c53

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_pullback_curveChange_of_iso_of_nodes_fixed
import Definitions.Def_AlgebraicGeometry_TwoGluedCurvesNodeUnitModule
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Theorems.Thm_AlgebraicGeometry_exists_rationalPoint_enumeration_of_natCard_pullback_eq
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_isNodeUnitModule_one_unit
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_exists_isInvertible_isNodeUnitModule
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_nonempty_iso
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_pullback_baseChangeSnd
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_tensor
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_smul_units
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_exists_isNodeUnitModule_of_pullback_curveChange_iso_unit
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_exists_eq_mul_of_iso
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_nonempty_pullback_curveChange_iso_unit
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_fibrewiseAlgEquivZero
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_pullback_pullback_of_rigidify_iso_unit
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_pullbackAlong_mul_iso
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_pullbackAlong_one_iso
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_postComp_transport_eq_self_of_ker_restrictPair_of_iso_comp_eq_of_crossing_of_twoGluedSmoothCurves
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add"

set_option autoImplicit false

universe u v

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_postComp_transport_eq_self_of_ker_restrictPair_of_iso_comp_eq_of_crossing_of_twoGluedSmoothCurves.AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_postComp_transport_eq_self_of_ker_restrictPair_of_iso_comp_eq_of_crossing_of_twoGluedSmoothCurves.AlgebraicGeometry.RelPicard AlgebraicGeometry.SplitTorus"

open AlgebraicGeometry.TwoGluedCurves

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "SmoothOfRelativeDimension IsProper Scheme.Modules.pullback GeometricallyIntegral Spec Scheme IsClosedImmersion IsReduced Scheme.Modules.pullbackCongr Scheme.Modules.pullbackId Scheme.Modules Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso Scheme.Modules.isInvertible_unit Scheme.Modules.rigidify exists_rationalPoint_enumeration_of_natCard_pullback_eq Scheme.Modules.IsInvertible.nonempty_iso_pullback_pullback_of_rigidify_iso_unit"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "rigSection postComp RigidifiedLineBundle RepresentsRelSubPic FibrewiseAlgEquivZero algEquivZeroCut algEquivZeroGroupCut RepresentsRelSubPic.relativeGroupLaw curveChange rigSection_curveChange RepresentsRelSubPic.pullbackHom RepresentsRelSubPic.postComp_pullbackHom_classify rigSection_snd RepresentsRelSubPic.nonempty_pullbackAlong_one_iso"
namespace GtfAssembly
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

variable {k : Type u} [Field k]

section restrict

variable {X C₁ : Scheme.{u}} {x : X ⟶ Spec (CommRingCat.of k)} {c₁ : C₁ ⟶ Spec (CommRingCat.of k)}
  (i₁ : SchemeHomOver c₁ x)
  {ε : SchemeHomOver (𝟙 _) x} {ε₁ : SchemeHomOver (𝟙 _) c₁} (hε : ε₁.1 ≫ i₁.1 = ε.1)
  {D : RelativePic0Designation k x} (hD : RepresentsRelSubPic x ε (algEquivZeroCut x ε) D)
  {D₁ : RelativePic0Designation k c₁} (hD₁ : RepresentsRelSubPic c₁ ε₁ (algEquivZeroCut c₁ ε₁) D₁)

theorem classify_poincare_pullbackAlong {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (a : SchemeHomOver t D.toBase) :
    hD.classify t (hD.poincare.pullbackAlong a)
      ((algEquivZeroCut x ε).pullback_mem _ _ a _ hD.poincare_mem) = a :=
  (hD.classify_unique t _ _ a ⟨Iso.refl _⟩).symm

include hε in

theorem nonempty_poincare_pullbackAlong_comp_pullbackHom_iso {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (a : SchemeHomOver t D.toBase) :
    Nonempty ((hD₁.poincare.pullbackAlong
        (NeronModelInfra.schemeHomOverComp a (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε hD hD₁))).L ≅
      (Scheme.Modules.pullback (curveChange i₁.1 i₁.2 t)).obj (hD.poincare.pullbackAlong a).L) := by
  have h1 : NeronModelInfra.schemeHomOverComp a (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε hD hD₁) =
      postComp (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε hD hD₁)
        (hD.classify t (hD.poincare.pullbackAlong a)
          ((algEquivZeroCut x ε).pullback_mem _ _ a _ hD.poincare_mem)) := by
    rw [classify_poincare_pullbackAlong]; rfl
  rw [h1, RepresentsRelSubPic.postComp_pullbackHom_classify]
  exact hD₁.classify_spec t _ _

include hε in

theorem comp_pullbackHom_eq_one_iff {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (a : SchemeHomOver t D.toBase) :
    NeronModelInfra.schemeHomOverComp a (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε hD hD₁) =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₁ ε₁) hD₁).one t ↔
      Nonempty ((Scheme.Modules.pullback (curveChange i₁.1 i₁.2 t)).obj (hD.poincare.pullbackAlong a).L ≅
        SheafOfModules.unit (pullback c₁ t).ringCatSheaf) := by
  obtain ⟨e⟩ := nonempty_poincare_pullbackAlong_comp_pullbackHom_iso i₁ hε hD hD₁ t a
  obtain ⟨e1⟩ := RepresentsRelSubPic.nonempty_pullbackAlong_one_iso (P := algEquivZeroGroupCut c₁ ε₁) hD₁ t
  constructor
  · intro h
    rw [h] at e
    exact ⟨e.symm ≪≫ e1⟩
  · rintro ⟨f⟩
    exact hD₁.ext_of_iso t _ _ ⟨e ≪≫ f ≪≫ e1.symm⟩

end restrict

section restrict₂

variable {X C₂ : Scheme.{u}} {x : X ⟶ Spec (CommRingCat.of k)} {c₂ : C₂ ⟶ Spec (CommRingCat.of k)}
  (i₂ : SchemeHomOver c₂ x)
  {ε : SchemeHomOver (𝟙 _) x} {ε₂ : SchemeHomOver (𝟙 _) c₂}
  {D : RelativePic0Designation k x} (hD : RepresentsRelSubPic x ε (algEquivZeroCut x ε) D)
  {D₂ : RelativePic0Designation k c₂} (hD₂ : RepresentsRelSubPic c₂ ε₂ (algEquivZeroCut c₂ ε₂) D₂)
  (ν₂ : SchemeHomOver D.toBase D₂.toBase)
  (hν₂ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (a : SchemeHomOver t D.toBase),
      Nonempty ((hD₂.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a ν₂)).L ≅
        Scheme.Modules.rigidify (rigSection c₂ t ε₂) (pullback.snd c₂ t)
          ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 t)).obj (hD.poincare.pullbackAlong a).L)))

include hν₂ in

theorem comp_ν₂_eq_one_iff {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (a : SchemeHomOver t D.toBase) :
    NeronModelInfra.schemeHomOverComp a ν₂ =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₂ ε₂) hD₂).one t ↔
      Nonempty (Scheme.Modules.rigidify (rigSection c₂ t ε₂) (pullback.snd c₂ t)
          ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 t)).obj (hD.poincare.pullbackAlong a).L) ≅
        SheafOfModules.unit (pullback c₂ t).ringCatSheaf) := by
  obtain ⟨e⟩ := hν₂ t a
  obtain ⟨e1⟩ := RepresentsRelSubPic.nonempty_pullbackAlong_one_iso (P := algEquivZeroGroupCut c₂ ε₂) hD₂ t
  constructor
  · intro h
    rw [h] at e
    exact ⟨e.symm ≪≫ e1⟩
  · rintro ⟨f⟩
    exact hD₂.ext_of_iso t _ _ ⟨e ≪≫ f ≪≫ e1.symm⟩

end restrict₂

end AlgebraicGeometry.RelPicard.GtfAssembly

end

open AlgebraicGeometry.RelPicard.GtfAssembly in
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
    (D₂ : RelativePic0Designation k c₂) (hD₂ : RepresentsRelSubPic c₂ ε₂ (algEquivZeroCut c₂ ε₂) D₂)
    (ν₁ : SchemeHomOver D.toBase D₁.toBase) (ν₂ : SchemeHomOver D.toBase D₂.toBase)
    (hν₁ : ν₁ = RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε hD hD₁)
    (hν₂ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (a : SchemeHomOver t D.toBase),
        Nonempty ((hD₂.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a ν₂)).L ≅
          Scheme.Modules.rigidify (rigSection c₂ t ε₂) (pullback.snd c₂ t)
            ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 t)).obj (hD.poincare.pullbackAlong a).L)))

    (ws : X ≅ X) (hws : ws.hom ≫ x = x) (hws' : ws.inv ≫ x = x)
    (α₁ : C₁ ≅ C₁) (hα₁ : α₁.hom ≫ c₁ = c₁) (hα₁i : α₁.hom ≫ i₁.1 = i₁.1 ≫ ws.hom)
    (α₂ : C₂ ≅ C₂) (hα₂ : α₂.hom ≫ c₂ = c₂) (hα₂i : α₂.hom ≫ i₂.1 = i₂.1 ≫ ws.hom)
    (hcross : ∀ z : Spec (CommRingCat.of k) ⟶ pullback i₁.1 i₂.1, z ≫ pullback.fst i₁.1 i₂.1 ≫ i₁.1 ≫ ws.hom = z ≫ pullback.fst i₁.1 i₂.1 ≫ i₁.1)

    (θs : SchemeHomOver D.toBase D.toBase)
    (hθs : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
        (M : RigidifiedLineBundle x ε t) (hM : FibrewiseAlgEquivZero M) (N : RigidifiedLineBundle x ε t) (hN : FibrewiseAlgEquivZero N)
        (Q : T.Modules), Scheme.Modules.IsInvertible Q →
        Nonempty (N.L ≅ (Scheme.Modules.pullback (curveChange (c := x) (c' := x) ws.hom hws t)).obj M.L ⊗
          (Scheme.Modules.pullback (pullback.snd x t)).obj Q) →
        postComp θs (hD.classify t M hM) = hD.classify t N hN) :
    ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (a : SchemeHomOver t D.toBase),
      NeronModelInfra.schemeHomOverComp a ν₁ =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₁ ε₁) hD₁).one t →
      NeronModelInfra.schemeHomOverComp a ν₂ =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₂ ε₂) hD₂).one t →
      postComp θs a = a := by
  classical
  haveI : IsReduced X := hXred

  obtain ⟨p₁, p₂, hinj, hnode, hinter⟩ :=
    AlgebraicGeometry.exists_rationalPoint_enumeration_of_natCard_pullback_eq k x i₁ i₂ s hs hs0

  have hfix : ∀ j, ((p₁ j).1 ≫ i₁.1) ≫ ws.hom = (p₁ j).1 ≫ i₁.1 := fun j => by
    have := hcross (pullback.lift (p₁ j).1 (p₂ j).1 (hnode j))
    simpa only [pullback.lift_fst_assoc, Category.assoc] using this
  have hα₁p : ∀ j, (p₁ j).1 ≫ α₁.hom = (p₁ j).1 := fun j => by
    rw [← cancel_mono i₁.1, Category.assoc, hα₁i, ← Category.assoc, hfix]
  have hα₂p : ∀ j, (p₂ j).1 ≫ α₂.hom = (p₂ j).1 := fun j => by
    rw [← cancel_mono i₂.1, Category.assoc, hα₂i, ← Category.assoc, ← hnode j, hfix]
  intro T t a h1 h2

  rw [hν₁, comp_pullbackHom_eq_one_iff i₁ hε hD hD₁ t] at h1
  obtain ⟨f₁⟩ := h1
  rw [comp_ν₂_eq_one_iff i₂ hD hD₂ ν₂ hν₂ t] at h2
  obtain ⟨g₂⟩ := h2
  have hPinv : Scheme.Modules.IsInvertible (hD.poincare.pullbackAlong a).L := (hD.poincare.pullbackAlong a).isInvertible
  obtain ⟨r⟩ := Scheme.Modules.IsInvertible.nonempty_iso_pullback_pullback_of_rigidify_iso_unit
    (rigSection c₂ t ε₂) (pullback.snd c₂ t) (hPinv.pullback (curveChange i₂.1 i₂.2 t)) ⟨g₂⟩
  have n12 : nodeSectionFst p₁ t ⟨0, hs0⟩ ≫ curveChange i₁.1 i₁.2 t =
      nodeSectionSnd p₂ t ⟨0, hs0⟩ ≫ curveChange i₂.1 i₂.2 t := by
    simp only [nodeSectionFst, nodeSectionSnd]
    rw [rigSection_curveChange i₁.1 i₁.2 (ε := ⟨(p₁ ⟨0, hs0⟩).1 ≫ i₁.1, by
          rw [Category.assoc, i₁.2]; exact (p₁ ⟨0, hs0⟩).2⟩) rfl,
      rigSection_curveChange i₂.1 i₂.2 (ε := ⟨(p₁ ⟨0, hs0⟩).1 ≫ i₁.1, by
          rw [Category.assoc, i₁.2]; exact (p₁ ⟨0, hs0⟩).2⟩) (hnode ⟨0, hs0⟩).symm]
  have hN : Nonempty ((Scheme.Modules.pullback (rigSection c₂ t ε₂)).obj
      ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 t)).obj (hD.poincare.pullbackAlong a).L) ≅
        SheafOfModules.unit T.ringCatSheaf) := by
    have s₂ : nodeSectionSnd p₂ t ⟨0, hs0⟩ ≫ pullback.snd c₂ t = 𝟙 T := rigSection_snd _ _
    refine ⟨?_⟩
    refine ((Scheme.Modules.pullbackId _).app _).symm ≪≫ (Scheme.Modules.pullbackCongr s₂.symm).app _ ≪≫
      ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
      ((Scheme.Modules.pullback (nodeSectionSnd p₂ t ⟨0, hs0⟩)).mapIso r).symm ≪≫
      (Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackCongr n12.symm).app _ ≪≫
      ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
      (Scheme.Modules.pullback (nodeSectionFst p₁ t ⟨0, hs0⟩)).mapIso f₁ ≪≫ Scheme.Modules.pullbackUnitIso _
  have f₂ : (Scheme.Modules.pullback (curveChange i₂.1 i₂.2 t)).obj (hD.poincare.pullbackAlong a).L ≅
      SheafOfModules.unit (pullback c₂ t).ringCatSheaf :=
    r ≪≫ (Scheme.Modules.pullback _).mapIso hN.some ≪≫ Scheme.Modules.pullbackUnitIso _

  obtain ⟨u, hu⟩ := exists_isNodeUnitModule_of_pullback_curveChange_iso_unit k x i₁ i₂ hjs p₁ p₂ hinj hnode
    hinter hcr t _ hPinv ⟨f₁⟩ ⟨f₂⟩

  have hu' := IsNodeUnitModule.pullback_curveChange_of_iso_of_nodes_fixed x i₁ i₂ p₁ p₂ ws hws α₁ hα₁ hα₁i α₂ hα₂ hα₂i
    hα₁p hα₂p t u _ hu
  obtain ⟨ee⟩ := IsNodeUnitModule.nonempty_iso hu hu'

  have hmem := (algEquivZeroCut x ε).pullback_mem _ _ a _ hD.poincare_mem
  have key := hθs t (hD.poincare.pullbackAlong a) hmem (hD.poincare.pullbackAlong a) hmem
    (SheafOfModules.unit T.ringCatSheaf) (Scheme.Modules.isInvertible_unit T)
    ⟨ee ≪≫ (ρ_ _).symm ≪≫ (Iso.refl _ ⊗ᵢ (Scheme.Modules.pullbackUnitIso _).symm)⟩
  rw [classify_poincare_pullbackAlong] at key
  exact key

end S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_postComp_transport_eq_self_of_ker_restrictPair_of_iso_comp_eq_of_crossing_of_twoGluedSmoothCurves
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_postComp_transport_eq_self_of_ker_restrictPair_of_iso_comp_eq_of_crossing_of_twoGluedSmoothCurves (solution)
