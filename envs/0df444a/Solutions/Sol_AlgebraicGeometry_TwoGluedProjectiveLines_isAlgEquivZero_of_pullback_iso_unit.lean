-- Prove2me | solution 1 for AlgebraicGeometry.TwoGluedProjectiveLines.isAlgEquivZero_of_pullback_iso_unit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/efe13819-06ff-5ff2-8e6c-ce937bf72abd

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_TwoGluedProjectiveLinesNodeUnitModule
import Theorems.Thm_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_TwoGluedProjectiveLines_isNodeUnitModule_one_unit
import Theorems.Thm_AlgebraicGeometry_TwoGluedProjectiveLines_exists_isInvertible_isNodeUnitModule
import Theorems.Thm_AlgebraicGeometry_TwoGluedProjectiveLines_IsNodeUnitModule_pullback_baseChangeSnd
import Theorems.Thm_AlgebraicGeometry_TwoGluedProjectiveLines_IsNodeUnitModule_nonempty_iso
import Theorems.Thm_AlgebraicGeometry_TwoGluedProjectiveLines_exists_isNodeUnitModule_pullback_of_pullback_iso_unit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_TwoGluedProjectiveLines_isAlgEquivZero_of_pullback_iso_unit
p2m_attr_erase "instance" "PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve NeronModelInfra AlgebraicGeometry.TwoGluedProjectiveLines

noncomputable section

namespace TwoGluedLinesSocketAux

p2m_open "Polynomial AlgebraicGeometry.Polynomial"

variable {κ : Type u} [Field κ] {s : ℕ} (lam : Fin s → κˣ)

def lineFactor (i : Fin s) : κ[X] := C 1 + X * C ((lam i : κ) - 1)

def linePoly : κ[X] := ∏ i, lineFactor lam i

lemma lineFactor_dvd (i : Fin s) : lineFactor lam i ∣ linePoly lam :=
  Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

@[scoped simp] lemma aeval_zero_lineFactor (i : Fin s) : aeval (0 : κ) (lineFactor lam i) = 1 := by
  simp [lineFactor]

@[scoped simp] lemma aeval_one_lineFactor (i : Fin s) : aeval (1 : κ) (lineFactor lam i) = lam i := by
  simp [lineFactor]

@[scoped simp] lemma aeval_zero_linePoly : aeval (0 : κ) (linePoly lam) = 1 := by
  simp [linePoly, map_prod]

@[scoped simp] lemma aeval_one_linePoly : aeval (1 : κ) (linePoly lam) = ∏ i, (lam i : κ) := by
  simp [linePoly, map_prod]

lemma linePoly_ne_zero : linePoly lam ≠ 0 := by
  intro h
  have := aeval_zero_linePoly lam
  rw [h, map_zero] at this
  exact zero_ne_one this

lemma isUnit_aeval_zero_linePoly : IsUnit (aeval (0 : κ) (linePoly lam)) := by
  rw [aeval_zero_linePoly]; exact isUnit_one

lemma isUnit_aeval_one_linePoly : IsUnit (aeval (1 : κ) (linePoly lam)) := by
  rw [aeval_one_linePoly]
  exact IsUnit.mk0 _ (Finset.prod_ne_zero_iff.mpr fun i _ => (lam i).ne_zero)

abbrev Λ : Type u := Localization.Away (linePoly lam)

scoped instance : IsDomain (Λ lam) :=
  IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors (linePoly_ne_zero lam))

scoped instance : Algebra.FiniteType κ (Λ lam) := inferInstance

lemma isUnit_lineFactor (i : Fin s) : IsUnit (algebraMap κ[X] (Λ lam) (lineFactor lam i)) :=
  isUnit_of_dvd_unit (map_dvd _ (lineFactor_dvd lam i)) (IsLocalization.Away.algebraMap_isUnit _)

def glueUnit (i : Fin s) : (Λ lam)ˣ := (isUnit_lineFactor lam i).unit

@[scoped simp] lemma val_glueUnit (i : Fin s) :
    (glueUnit lam i : Λ lam) = algebraMap κ[X] (Λ lam) (lineFactor lam i) := rfl

def evalHom (c : κ) (hc : IsUnit (aeval c (linePoly lam))) : Λ lam →+* κ :=
  Localization.awayLift (aeval c : κ[X] →ₐ[κ] κ).toRingHom (linePoly lam) hc

lemma evalHom_algebraMap (c : κ) (hc : IsUnit (aeval c (linePoly lam))) (q : κ[X]) :
    evalHom lam c hc (algebraMap κ[X] (Λ lam) q) = aeval c q :=
  IsLocalization.Away.lift_eq _ hc q

lemma evalHom_comp_algebraMap (c : κ) (hc : IsUnit (aeval c (linePoly lam))) :
    (evalHom lam c hc).comp (algebraMap κ (Λ lam)) = RingHom.id κ := by
  ext r
  rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply κ κ[X] (Λ lam), evalHom_algebraMap]
  simp

end TwoGluedLinesSocketAux
p2m_reactivate "P2MW.S_AlgebraicGeometry_TwoGluedProjectiveLines_isAlgEquivZero_of_pullback_iso_unit.TwoGluedLinesSocketAux"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_TwoGluedProjectiveLines_isAlgEquivZero_of_pullback_iso_unit.TwoGluedLinesSocketAux"

open TwoGluedLinesSocketAux in
theorem solution
    (κ : Type u) [Field κ] [IsAlgClosed κ] [DecidableEq (RatFunc κ)]
    {X : Scheme.{u}} (x : X ⟶ Spec (.of κ)) [IsReduced X] [IsSeparated x]
    (M₁ M₂ : CurveModel κ (RatFunc κ)) (i₁ : M₁.C ⟶ X) (i₂ : M₂.C ⟶ X)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (hi₁ : i₁ ≫ x = M₁.toBase) (hi₂ : i₂ ≫ x = M₂.toBase)
    (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    {s : ℕ} (a b : Fin s → κˣ) (ha : Function.Injective a)
    (hnode : ∀ i, i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint κ (a i : κ))).1
                = i₂.base (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint κ (b i : κ))).1)
    (hinter : ∀ p q, i₁.base p = i₂.base q →
      ∃ i, p = (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint κ (a i))).1 ∧
        q = (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint κ (b i))).1)
    (htrans : IsReduced (pullback i₁ i₂))
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (h₁ : Nonempty ((Scheme.Modules.pullback i₁).obj L ≅
      (Scheme.Modules.pullback i₁).obj (SheafOfModules.unit X.ringCatSheaf)))
    (h₂ : Nonempty ((Scheme.Modules.pullback i₂).obj L ≅
      (Scheme.Modules.pullback i₂).obj (SheafOfModules.unit X.ringCatSheaf))) :
    IsAlgEquivZero x L := by

  obtain ⟨lam, hlam⟩ := exists_isNodeUnitModule_pullback_of_pullback_iso_unit κ x M₁ M₂ i₁ i₂ hi₁ hi₂
    hcover a b ha hnode hinter htrans L hL h₁ h₂

  let hΛ : Spec (.of (Λ lam)) ⟶ Spec (.of κ) := Spec.map (CommRingCat.ofHom (algebraMap κ (Λ lam)))
  haveI hft : LocallyOfFiniteType hΛ := by
    refine (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr ?_
    change (algebraMap κ (Λ lam)).FiniteType
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  have hgi : GeometricallyIntegral hΛ := AlgebraicGeometry.geometricallyIntegral_of_isAlgClosed hΛ

  let tPt : ∀ (c : κ) (hc : IsUnit (Polynomial.aeval c (linePoly lam))), SchemeHomOver (𝟙 (Spec (.of κ))) hΛ :=
    fun c hc => ⟨Spec.map (CommRingCat.ofHom (evalHom lam c hc)), by
      change Spec.map _ ≫ Spec.map _ = _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, evalHom_comp_algebraMap]
      exact Spec.map_id _⟩
  let t₀ := tPt 0 (isUnit_aeval_zero_linePoly lam)
  let t₁ := tPt 1 (isUnit_aeval_one_linePoly lam)

  let ι : Λ lam →* Γ(Spec (.of (Λ lam)), ⊤) := (Scheme.ΓSpecIso (.of (Λ lam))).inv.hom.toMonoidHom
  let u : Fin s → Γ(Spec (.of (Λ lam)), ⊤)ˣ := fun i => Units.map ι (glueUnit lam i)
  obtain ⟨M, hMinv, hM⟩ := exists_isInvertible_isNodeUnitModule κ x M₁ M₂ i₁ i₂ hi₁ hi₂ hcover a b ha
    hnode hinter htrans hΛ u

  have key : ∀ (c : κ) (hc : IsUnit (Polynomial.aeval c (linePoly lam))) (i : Fin s),
      Units.map (tPt c hc).1.appTop.hom.toMonoidHom (u i) =
        Units.map (Scheme.ΓSpecIso (.of κ)).inv.hom.toMonoidHom
          (Units.map (evalHom lam c hc).toMonoidHom (glueUnit lam i)) := by
    intro c hc i
    ext
    change (Spec.map (CommRingCat.ofHom (evalHom lam c hc))).appTop.hom
        ((Scheme.ΓSpecIso (.of (Λ lam))).inv.hom (glueUnit lam i : Λ lam)) =
      (Scheme.ΓSpecIso (.of κ)).inv.hom (evalHom lam c hc (glueUnit lam i : Λ lam))
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
    rfl
  have hu₀ : (fun i => Units.map t₀.1.appTop.hom.toMonoidHom (u i)) =
      (1 : Fin s → Γ(Spec (.of κ), ⊤)ˣ) := by
    funext i
    rw [key, Pi.one_apply]
    have : Units.map (evalHom lam 0 (isUnit_aeval_zero_linePoly lam)).toMonoidHom (glueUnit lam i) = 1 := by
      ext
      change evalHom lam 0 _ (glueUnit lam i : Λ lam) = 1
      rw [val_glueUnit, evalHom_algebraMap, aeval_zero_lineFactor]
    rw [this, map_one]
  have hu₁ : (fun i => Units.map t₁.1.appTop.hom.toMonoidHom (u i)) =
      fun i => Units.map (Scheme.ΓSpecIso (.of κ)).inv.hom.toMonoidHom (lam i) := by
    funext i
    rw [key]
    have : Units.map (evalHom lam 1 (isUnit_aeval_one_linePoly lam)).toMonoidHom (glueUnit lam i) =
        lam i := by
      ext
      change evalHom lam 1 _ (glueUnit lam i : Λ lam) = lam i
      rw [val_glueUnit, evalHom_algebraMap, aeval_one_lineFactor]
    rw [this]
  have hM₀ := IsNodeUnitModule.pullback_baseChangeSnd κ x M₁ M₂ i₁ i₂ hi₁ hi₂ hcover a b ha hnode hinter
    htrans hMinv hM t₀
  rw [hu₀] at hM₀
  have hM₁ := IsNodeUnitModule.pullback_baseChangeSnd κ x M₁ M₂ i₁ i₂ hi₁ hi₂ hcover a b ha hnode hinter
    htrans hMinv hM t₁
  rw [hu₁] at hM₁

  have hO := isNodeUnitModule_one_unit κ x M₁ M₂ i₁ i₂ hi₁ hi₂ hcover a b ha hnode hinter htrans
    (𝟙 (Spec (.of κ)))
  exact ⟨Spec (.of (Λ lam)), hΛ, hft, hgi, M, hMinv, t₀, t₁, hM₀.nonempty_iso hO, hM₁.nonempty_iso hlam⟩

end S_AlgebraicGeometry_TwoGluedProjectiveLines_isAlgEquivZero_of_pullback_iso_unit
end P2MW
export P2MW.S_AlgebraicGeometry_TwoGluedProjectiveLines_isAlgEquivZero_of_pullback_iso_unit (solution)
