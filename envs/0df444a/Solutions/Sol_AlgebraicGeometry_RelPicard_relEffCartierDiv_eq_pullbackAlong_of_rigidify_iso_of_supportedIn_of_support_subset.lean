-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.relEffCartierDiv_eq_pullbackAlong_of_rigidify_iso_of_supportedIn_of_support_subset
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/96227761-9ab8-57e6-bf90-abc84e312cd0

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import Definitions.Def_CategoryTheory_OverTotalPresheaf
import Definitions.Def_AlgebraicGeometry_LocalRepresentabilityULift
import Definitions.Def_AlgebraicGeometry_AffineLimit
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivFunctor
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivRestrict
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivTwist2
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicGeometry_ModulesRigidify

import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModuleMaps
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_nonempty_pullback_lineBundle_pullbackAlong_iso_of_supportedIn
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isIso_pullbackModuleComparison
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I_of_supportedIn
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_rigidify_pullback_tensor_iso
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_nonempty_rigidify_lineBundle_tensor_idealModule_pullbackAlong_iso_pullback_of_supportedIn
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_mul
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_comap_zeroSchemeIdeal
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_zeroSchemeIdeal_comp_eq_of_isIso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_relEffCartierDiv_eq_pullbackAlong_of_rigidify_iso_of_supportedIn_of_support_subset

set_option autoImplicit false

universe u

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.IdealSheafData.support_comap SmoothOfRelativeDimension IsProper Scheme.Modules.pullback Scheme.Hom LocallyOfFiniteType Spec Spec.map Scheme IsSeparated Scheme.Modules.pullbackCongr Scheme.fromSpecResidueField_apply Scheme.Modules.pullbackId Scheme.IdealSheafData.support_mul Scheme.Modules Scheme.Hom.comp_apply Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso RelPicard.baseChangeSnd RelPicard.rigSection Scheme.Modules.dual Scheme.IdealSheafData.module Scheme.IdealSheafData.invModule RelEffCartierDiv RelEffCartierDiv.ext mapOnProdOver mapOnProdOver_fst mapOnProdOver_snd RelEffCartierDiv.pullbackAlong_comp mapOnProdOver_snd_assoc Scheme.TwoAffineOpenCover Scheme.Modules.rigidify Scheme.Modules.rigidify_def Scheme.Modules.zeroSchemeIdeal Scheme.Modules.pullbackSection Scheme.Modules.pullbackSection_def Scheme.Modules.pullbackTensorObjIso Scheme.Modules.pullbackTensorUnitObjIso Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso RelEffCartierDiv.nonempty_pullback_lineBundle_pullbackAlong_iso_of_supportedIn Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison Scheme.IdealSheafData.IsInvertible RelEffCartierDiv.nonempty_rigidify_lineBundle_tensor_idealModule_pullbackAlong_iso_pullback_of_supportedIn Scheme.IdealSheafData.comap_mul Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd rigSection RigidifiedLineBundle fibreAt FibrewiseAlgEquivZero sectionIdeal sectionTwist fibreModule"
namespace FinTransport
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_relEffCartierDiv_eq_pullbackAlong_of_rigidify_iso_of_supportedIn_of_support_subset.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_relEffCartierDiv_eq_pullbackAlong_of_rigidify_iso_of_supportedIn_of_support_subset.AlgebraicGeometry.RelPicard NeronModelInfra"

theorem coe_support_zeroSchemeIdeal_pullbackSection {X X' : Scheme.{u}} (F : X' ⟶ X) {M : X.Modules}
    (hM : Scheme.Modules.IsInvertible M) (s : 𝟙_ X.Modules ⟶ M) :
    ((Scheme.Modules.zeroSchemeIdeal (Scheme.Modules.pullbackSection F s)).support : Set X') =
      F.base ⁻¹' ((Scheme.Modules.zeroSchemeIdeal s).support : Set X) := by
  rw [← hM.comap_zeroSchemeIdeal F, Scheme.IdealSheafData.support_comap]
  rfl

noncomputable def pullbackEquivOfIso {X X' : Scheme.{u}} (e : X' ≅ X) : X.Modules ≌ X'.Modules :=
  CategoryTheory.Equivalence.mk (Scheme.Modules.pullback e.hom) (Scheme.Modules.pullback e.inv)
    ((Scheme.Modules.pullbackComp e.inv e.hom ≪≫ Scheme.Modules.pullbackCongr e.inv_hom_id ≪≫
      Scheme.Modules.pullbackId X).symm)
    (Scheme.Modules.pullbackComp e.hom e.inv ≪≫ Scheme.Modules.pullbackCongr e.hom_inv_id ≪≫
      Scheme.Modules.pullbackId X')

scoped instance full_pullback_of_isIso {X X' : Scheme.{u}} (F : X' ⟶ X) [IsIso F] :
    (Scheme.Modules.pullback F).Full :=
  (pullbackEquivOfIso (asIso F)).full_functor

scoped instance faithful_pullback_of_isIso {X X' : Scheme.{u}} (F : X' ⟶ X) [IsIso F] :
    (Scheme.Modules.pullback F).Faithful :=
  (pullbackEquivOfIso (asIso F)).faithful_functor

theorem pullbackSection_ne_zero_of_isIso {X X' : Scheme.{u}} (F : X' ⟶ X) [IsIso F] {M : X.Modules}
    {s : 𝟙_ X.Modules ⟶ M} (hs : s ≠ 0) : Scheme.Modules.pullbackSection F s ≠ 0 := by
  intro h
  rw [Scheme.Modules.pullbackSection_def] at h
  have h1 : (Scheme.Modules.pullback F).map s = 0 := (Preadditive.IsIso.comp_left_eq_zero _ _).mp h
  exact hs ((Scheme.Modules.pullback F).map_injective
    (h1.trans ((Scheme.Modules.pullback F).map_zero _ _).symm))

theorem exists_pullbackSection_eq_of_isIso {X X' : Scheme.{u}} (F : X' ⟶ X) [IsIso F] {M : X.Modules}
    (τ : 𝟙_ X'.Modules ⟶ (Scheme.Modules.pullback F).obj M) :
    ∃ s : 𝟙_ X.Modules ⟶ M, Scheme.Modules.pullbackSection F s = τ := by
  refine ⟨(Scheme.Modules.pullback F).preimage ((Scheme.Modules.pullbackUnitIso F).hom ≫ τ), ?_⟩
  rw [Scheme.Modules.pullbackSection_def]
  erw [Functor.map_preimage]
  exact (Scheme.Modules.pullbackUnitIso F).inv_hom_id_assoc τ

theorem forall_support_subset_iff_of_isIso {Y Y' : Scheme.{u}} (F : Y' ⟶ Y) [IsIso F] {P : Y.Modules}
    (hP : Scheme.Modules.IsInvertible P) {P' : Y'.Modules} (j : P' ≅ (Scheme.Modules.pullback F).obj P)
    (V : Set Y) :
    (∀ σ' : 𝟙_ Y'.Modules ⟶ P', σ' ≠ 0 →
        ((Scheme.Modules.zeroSchemeIdeal σ').support : Set Y') ⊆ F.base ⁻¹' V) ↔
      (∀ σ : 𝟙_ Y.Modules ⟶ P, σ ≠ 0 → ((Scheme.Modules.zeroSchemeIdeal σ).support : Set Y) ⊆ V) := by
  constructor
  · intro h σ hσ
    have hσ' : Scheme.Modules.pullbackSection F σ ≫ j.inv ≠ 0 := fun h0 =>
      pullbackSection_ne_zero_of_isIso F hσ ((Preadditive.IsIso.comp_right_eq_zero _ _).mp h0)
    have := h _ hσ'
    rw [Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso,
      coe_support_zeroSchemeIdeal_pullbackSection F hP] at this
    exact F.homeomorph.surjective.preimage_subset_preimage_iff.mp this
  · intro h σ' hσ'
    obtain ⟨σ, hσ⟩ := exists_pullbackSection_eq_of_isIso F (σ' ≫ j.hom)
    have hσ0 : σ ≠ 0 := by
      intro hz
      apply hσ'
      have h1 : σ' ≫ j.hom = 0 := by
        rw [← hσ, Scheme.Modules.pullbackSection_def, hz]
        exact (congrArg ((Scheme.Modules.pullbackUnitIso F).inv ≫ ·)
          ((Scheme.Modules.pullback F).map_zero _ _)).trans comp_zero
      exact (Preadditive.IsIso.comp_right_eq_zero _ _).mp h1
    have := h σ hσ0
    rw [← Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso σ' j.hom, ← hσ,
      coe_support_zeroSchemeIdeal_pullbackSection F hP]
    exact Set.preimage_mono this

abbrev FinerAt {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) (U : C.Opens)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : (pullback c t).Modules)
    {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T) : Prop :=
  ∀ σ : 𝟙_ (pullback c (s ≫ t)).Modules ⟶ (Scheme.Modules.pullback (mapOnProdOver c s rfl)).obj M,
    σ ≠ 0 → ((Scheme.Modules.zeroSchemeIdeal σ).support : Set ↥(pullback c (s ≫ t))) ⊆
      ((pullback.fst c (s ≫ t)) ⁻¹ᵁ U : Set ↥(pullback c (s ≫ t)))

theorem finerAt_transport {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (U : C.Opens) {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : SchemeHomOver t' t) (M : (pullback c t).Modules) (hM : Scheme.Modules.IsInvertible M)
    (M' : (pullback c t').Modules) (i : M' ≅ (Scheme.Modules.pullback (baseChangeSnd c ψ)).obj M)
    {k : Type u} [Field k] (x' : Spec (CommRingCat.of k) ⟶ T') :
    FinerAt c U t' M' x' ↔ FinerAt c U t M (x' ≫ ψ.1) := by
  obtain ⟨ψ1, hψ⟩ := ψ
  subst hψ

  let e : pullback c (x' ≫ ψ1 ≫ t) ≅ pullback c ((x' ≫ ψ1) ≫ t) :=
    pullback.congrHom rfl (Category.assoc _ _ _).symm
  have he_fst : e.hom ≫ pullback.fst c ((x' ≫ ψ1) ≫ t) = pullback.fst c (x' ≫ ψ1 ≫ t) := by
    rw [pullback.congrHom_hom, pullback.lift_fst, Category.comp_id]
  have hE : mapOnProdOver c x' rfl ≫ baseChangeSnd c (⟨ψ1, rfl⟩ : SchemeHomOver (ψ1 ≫ t) t) =
      e.hom ≫ mapOnProdOver c (x' ≫ ψ1) rfl := by
    apply pullback.hom_ext
    · simp only [e, Category.assoc, mapOnProdOver_fst, pullback.congrHom_hom, baseChangeSnd, pullback.lift_fst,
        Category.comp_id]
    · simp only [e, Category.assoc, mapOnProdOver_snd, pullback.congrHom_hom, baseChangeSnd, pullback.lift_snd,
        Category.comp_id, mapOnProdOver_snd_assoc, pullback.lift_snd_assoc]
  have hP : Scheme.Modules.IsInvertible
      ((Scheme.Modules.pullback (mapOnProdOver c (x' ≫ ψ1) rfl)).obj M) :=
    hM.pullback _
  let j : (Scheme.Modules.pullback (mapOnProdOver c x' rfl)).obj M' ≅
      (Scheme.Modules.pullback e.hom).obj ((Scheme.Modules.pullback (mapOnProdOver c (x' ≫ ψ1) rfl)).obj M) :=
    (Scheme.Modules.pullback (mapOnProdOver c x' rfl)).mapIso i ≪≫
      (Scheme.Modules.pullbackComp (mapOnProdOver c x' rfl) (baseChangeSnd c ⟨ψ1, rfl⟩)).app M ≪≫
      (Scheme.Modules.pullbackCongr hE).app M ≪≫
      ((Scheme.Modules.pullbackComp e.hom (mapOnProdOver c (x' ≫ ψ1) rfl)).app M).symm
  have hV : e.hom.base ⁻¹' ((pullback.fst c ((x' ≫ ψ1) ≫ t)) ⁻¹ᵁ U : Set ↥(pullback c ((x' ≫ ψ1) ≫ t))) =
      ((pullback.fst c (x' ≫ ψ1 ≫ t)) ⁻¹ᵁ U : Set ↥(pullback c (x' ≫ ψ1 ≫ t))) := by
    rw [← he_fst]
    rfl
  have key := forall_support_subset_iff_of_isIso e.hom hP j
    ((pullback.fst c ((x' ≫ ψ1) ≫ t)) ⁻¹ᵁ U : Set ↥(pullback c ((x' ≫ ψ1) ≫ t)))
  rw [hV] at key
  exact key

end AlgebraicGeometry.RelPicard.FinTransport
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_relEffCartierDiv_eq_pullbackAlong_of_rigidify_iso_of_supportedIn_of_support_subset.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_relEffCartierDiv_eq_pullbackAlong_of_rigidify_iso_of_supportedIn_of_support_subset.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_relEffCartierDiv_eq_pullbackAlong_of_rigidify_iso_of_supportedIn_of_support_subset.AlgebraicGeometry.RelPicard.FinTransport"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_relEffCartierDiv_eq_pullbackAlong_of_rigidify_iso_of_supportedIn_of_support_subset.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_relEffCartierDiv_eq_pullbackAlong_of_rigidify_iso_of_supportedIn_of_support_subset.AlgebraicGeometry.RelPicard"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_relEffCartierDiv_eq_pullbackAlong_of_rigidify_iso_of_supportedIn_of_support_subset.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.IdealSheafData.support_comap SmoothOfRelativeDimension IsProper Scheme.Modules.pullback Scheme.Hom LocallyOfFiniteType Spec Spec.map Scheme IsSeparated Scheme.Modules.pullbackCongr Scheme.fromSpecResidueField_apply Scheme.Modules.pullbackId Scheme.IdealSheafData.support_mul Scheme.Modules Scheme.Hom.comp_apply Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso RelPicard.baseChangeSnd RelPicard.rigSection Scheme.Modules.dual Scheme.IdealSheafData.module Scheme.IdealSheafData.invModule RelEffCartierDiv RelEffCartierDiv.ext mapOnProdOver mapOnProdOver_fst mapOnProdOver_snd RelEffCartierDiv.pullbackAlong_comp mapOnProdOver_snd_assoc Scheme.TwoAffineOpenCover Scheme.Modules.rigidify Scheme.Modules.rigidify_def Scheme.Modules.zeroSchemeIdeal Scheme.Modules.pullbackSection Scheme.Modules.pullbackSection_def Scheme.Modules.pullbackTensorObjIso Scheme.Modules.pullbackTensorUnitObjIso Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso RelEffCartierDiv.nonempty_pullback_lineBundle_pullbackAlong_iso_of_supportedIn Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison Scheme.IdealSheafData.IsInvertible RelEffCartierDiv.nonempty_rigidify_lineBundle_tensor_idealModule_pullbackAlong_iso_pullback_of_supportedIn Scheme.IdealSheafData.comap_mul Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd rigSection RigidifiedLineBundle fibreAt FibrewiseAlgEquivZero sectionIdeal sectionTwist fibreModule"
namespace K5bSupplyE
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_relEffCartierDiv_eq_pullbackAlong_of_rigidify_iso_of_supportedIn_of_support_subset.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_relEffCartierDiv_eq_pullbackAlong_of_rigidify_iso_of_supportedIn_of_support_subset.AlgebraicGeometry.RelPicard NeronModelInfra"

variable (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsSeparated c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    {ρ : ℕ} (E : RelEffCartierDiv c ρ (𝟙 (Spec (CommRingCat.of R)))) (hEU : E.SupportedIn U)

theorem pullbackAlong_congr_hom {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {n : ℕ} {T T' : Scheme.{u}} {g : T ⟶ S}
    {g' : T' ⟶ S} (D : RelEffCartierDiv f n g') {φ₁ φ₂ : T ⟶ T'} (h : φ₁ = φ₂) (h₁ : φ₁ ≫ g' = g)
    (h₂ : φ₂ ≫ g' = g) : D.pullbackAlong φ₁ h₁ = D.pullbackAlong φ₂ h₂ := by
  subst h; rfl

theorem pullbackAlong_I_eq_mul {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {n m l : ℕ}
    {T' : Scheme.{u}} {g' : T' ⟶ S} (D : RelEffCartierDiv f n g') (D₀ : RelEffCartierDiv f m g') (F : RelEffCartierDiv f l g')
    (hD : D.I = D₀.I * F.I) {T : Scheme.{u}} {g : T ⟶ S} (φ : T ⟶ T') (hφ : φ ≫ g' = g) :
    (D.pullbackAlong φ hφ).I = (D₀.pullbackAlong φ hφ).I * (F.pullbackAlong φ hφ).I := by
  change D.I.comap _ = D₀.I.comap _ * F.I.comap _
  rw [hD, Scheme.IdealSheafData.comap_mul]

include hEU in

theorem isInvertible_EI {V : Scheme.{u}} (u : V ⟶ Spec (CommRingCat.of R)) :
    (E.pullbackAlong u (Category.comp_id u)).I.IsInvertible :=
  (E.pullbackAlong u (Category.comp_id u)).isInvertible_I_of_supportedIn U (hEU.pullbackAlong u (Category.comp_id u))

include hEU in

theorem isInvertible_ElineBundle {V : Scheme.{u}} (u : V ⟶ Spec (CommRingCat.of R)) :
    Scheme.Modules.IsInvertible (E.pullbackAlong u (Category.comp_id u)).lineBundle :=
  (isInvertible_EI R c U E hEU u).isInvertible_invModule

include hEU in

theorem isInvertible_Mγ {e : ℕ} {V : Scheme.{u}} (u : V ⟶ Spec (CommRingCat.of R))
    (LV : RigidifiedLineBundle c ε u) (DγV : RelEffCartierDiv c e u) (hDγV : DγV.SupportedIn U) :
    Scheme.Modules.IsInvertible (LV.L ⊗ ((E.pullbackAlong u (Category.comp_id u)).lineBundle ⊗ DγV.idealModule)) :=
  LV.isInvertible.tensor ((isInvertible_ElineBundle R c U E hEU u).tensor (DγV.isInvertible_I_of_supportedIn U
    hDγV).isInvertible_module)

include hEU in

theorem exists_lineBundle_iso_of_rigidify_iso
    {g e : ℕ} {V : Scheme.{u}} (u : V ⟶ Spec (CommRingCat.of R))
    (LU : RigidifiedLineBundle c ε u) (DγU : RelEffCartierDiv c e u) (hDγU : DγU.SupportedIn U)
    (D₀ : RelEffCartierDiv c g u) (hD₀U : D₀.SupportedIn U) (D : RelEffCartierDiv c (g + e) u) (hD : D.I = D₀.I * DγU.I)
    (hDL : Nonempty (Scheme.Modules.rigidify (rigSection c u ε) (pullback.snd c u)
        (D.lineBundle ⊗ (E.pullbackAlong u (Category.comp_id u)).idealModule) ≅ LU.L)) :
    ∃ N : V.Modules, Scheme.Modules.IsInvertible N ∧
      Nonempty (D₀.lineBundle ≅ (LU.L ⊗ ((E.pullbackAlong u (Category.comp_id u)).lineBundle ⊗ DγU.idealModule)) ⊗
        (Scheme.Modules.pullback (pullback.snd c u)).obj N) := by
  have hEI : (E.pullbackAlong u (Category.comp_id u)).I.IsInvertible := isInvertible_EI R c U E hEU u
  have hD₀ : D₀.I.IsInvertible := D₀.isInvertible_I_of_supportedIn U hD₀U
  have hDγ : DγU.I.IsInvertible := DγU.isInvertible_I_of_supportedIn U hDγU
  have hDI : D.I.IsInvertible := by rw [hD]; exact hD₀.mul hDγ

  set F := (E.pullbackAlong u (Category.comp_id u)).idealModule with hF
  set X := D.lineBundle ⊗ F with hX
  have hXinv : Scheme.Modules.IsInvertible X := hDI.isInvertible_invModule.tensor hEI.isInvertible_module
  set N₀ : V.Modules := Scheme.Modules.dual ((Scheme.Modules.pullback (rigSection c u ε)).obj X) with hN₀
  have hN₀ : Scheme.Modules.IsInvertible N₀ := (hXinv.pullback _).dual.1

  refine ⟨Scheme.Modules.dual N₀, hN₀.dual.1, ?_⟩
  have cN : (Scheme.Modules.pullback (pullback.snd c u)).obj N₀ ⊗
      (Scheme.Modules.pullback (pullback.snd c u)).obj (Scheme.Modules.dual N₀) ≅ 𝟙_ _ :=
    (Scheme.Modules.pullbackTensorObjIso (pullback.snd c u) _ _).symm ≪≫
      (Scheme.Modules.pullback _).mapIso hN₀.dual.2.some ≪≫ Scheme.Modules.pullbackTensorUnitObjIso _

  have j0 : X ⊗ (Scheme.Modules.pullback (pullback.snd c u)).obj N₀ ≅ LU.L := by
    have h := hDL.some
    rw [Scheme.Modules.rigidify_def] at h
    exact h

  have j1 : X ≅ LU.L ⊗ (Scheme.Modules.pullback (pullback.snd c u)).obj (Scheme.Modules.dual N₀) :=
    (ρ_ X).symm ≪≫ (Iso.refl X ⊗ᵢ cN.symm) ≪≫ (α_ _ _ _).symm ≪≫ (j0 ⊗ᵢ Iso.refl _)

  have cST : F ⊗ (E.pullbackAlong u (Category.comp_id u)).lineBundle ≅ 𝟙_ _ := by
    rw [hF]; exact (hEI.isInvertible_module.dual).2.some
  have cγ : DγU.lineBundle ⊗ DγU.idealModule ≅ 𝟙_ _ :=
    (β_ _ _) ≪≫ (hDγ.isInvertible_module.dual).2.some

  have j2 : D.lineBundle ≅ (LU.L ⊗ (Scheme.Modules.pullback (pullback.snd c u)).obj (Scheme.Modules.dual N₀)) ⊗
      (E.pullbackAlong u (Category.comp_id u)).lineBundle :=
    (ρ_ _).symm ≪≫ (Iso.refl _ ⊗ᵢ cST.symm) ≪≫ (α_ _ _ _).symm ≪≫ ((show D.lineBundle ⊗ F ≅ _ from j1) ⊗ᵢ Iso.refl _)

  have i1 : D.lineBundle ≅ D₀.lineBundle ⊗ DγU.lineBundle :=
    eqToIso (congrArg Scheme.IdealSheafData.invModule hD) ≪≫ (hD₀.nonempty_mul_invModule_iso_tensor hDγ).some
  have j3 : D₀.lineBundle ≅ D.lineBundle ⊗ DγU.idealModule :=
    (ρ_ _).symm ≪≫ (Iso.refl _ ⊗ᵢ cγ.symm) ≪≫ (α_ _ _ _).symm ≪≫ (i1.symm ⊗ᵢ Iso.refl _)
  refine ⟨j3 ≪≫ (j2 ⊗ᵢ Iso.refl _) ≪≫ ?_⟩

  exact (α_ _ _ _) ≪≫ (α_ _ _ _) ≪≫ (Iso.refl _ ⊗ᵢ (β_ _ _)) ≪≫ (α_ _ _ _).symm

section Transport

variable {e : ℕ} (Dγ : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R)))) (hDγ : Dγ.SupportedIn U)
  {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (ψ1 : T' ⟶ T) (L : RigidifiedLineBundle c ε t)
  {k : Type u} [Field k] (s' : Spec (CommRingCat.of k) ⟶ T')

noncomputable def fibreIso : pullback (pullback.snd c t) (s' ≫ ψ1) ≅ pullback (pullback.snd c (ψ1 ≫ t)) s' :=
  pullbackLeftPullbackSndIso c t (s' ≫ ψ1) ≪≫ pullback.congrHom rfl (Category.assoc s' ψ1 t) ≪≫
    (pullbackLeftPullbackSndIso c (ψ1 ≫ t) s').symm

omit [IsSeparated c] in
theorem fibreIso_hom_fibreAt :
    (fibreIso R c t ψ1 s').hom ≫ fibreAt c (ψ1 ≫ t) s' = fibreAt c t (s' ≫ ψ1) := by
  simp only [fibreIso, fibreAt, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    pullbackLeftPullbackSndIso_inv_snd_snd, pullback.congrHom_hom, pullback.lift_snd,
    Category.comp_id, pullbackLeftPullbackSndIso_hom_snd]

omit [IsSeparated c] in
theorem fibreIso_hom_fst_baseChangeSnd :
    (fibreIso R c t ψ1 s').hom ≫ pullback.fst (pullback.snd c (ψ1 ≫ t)) s' ≫
        baseChangeSnd c (⟨ψ1, rfl⟩ : SchemeHomOver (ψ1 ≫ t) t) =
      pullback.fst (pullback.snd c t) (s' ≫ ψ1) := by
  have hβ : baseChangeSnd c (⟨ψ1, rfl⟩ : SchemeHomOver (ψ1 ≫ t) t) =
      pullback.lift (pullback.fst c (ψ1 ≫ t) ≫ 𝟙 C) (pullback.snd c (ψ1 ≫ t) ≫ ψ1) (by simp [pullback.condition]) := rfl
  rw [hβ]
  apply pullback.hom_ext
  · simp only [fibreIso, Iso.trans_hom, Iso.symm_hom, Category.assoc, pullback.lift_fst, Category.comp_id,
      pullbackLeftPullbackSndIso_inv_fst, pullback.congrHom_hom, pullbackLeftPullbackSndIso_hom_fst]
  · simp only [fibreIso, Iso.trans_hom, Iso.symm_hom, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
      pullbackLeftPullbackSndIso_inv_fst_snd_assoc, pullback.congrHom_hom,
      Category.comp_id, pullbackLeftPullbackSndIso_hom_snd_assoc, pullback.condition]

include hEU hDγ in

theorem nonempty_Mγ_iso_pullback :
    Nonempty ((L.pullbackAlong (⟨ψ1, rfl⟩ : SchemeHomOver (ψ1 ≫ t) t)).L ⊗
        ((E.pullbackAlong (ψ1 ≫ t) (Category.comp_id _)).lineBundle ⊗ (Dγ.pullbackAlong (ψ1 ≫ t) (Category.comp_id _)).idealModule) ≅
      (Scheme.Modules.pullback (baseChangeSnd c (⟨ψ1, rfl⟩ : SchemeHomOver (ψ1 ≫ t) t))).obj
        (L.L ⊗ ((E.pullbackAlong t (Category.comp_id t)).lineBundle ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule))) := by
  let ψ : SchemeHomOver (ψ1 ≫ t) t := ⟨ψ1, rfl⟩
  have hcomp : (Dγ.pullbackAlong t (Category.comp_id t)).pullbackAlong ψ1 ψ.2 =
      Dγ.pullbackAlong (ψ1 ≫ t) (Category.comp_id _) :=
    RelEffCartierDiv.pullbackAlong_comp _ _ _ _ _
  have hI : (Dγ.pullbackAlong (ψ1 ≫ t) (Category.comp_id _)).I =
      (Dγ.pullbackAlong t (Category.comp_id t)).I.comap (baseChangeSnd c ψ) := by
    rw [← hcomp]; rfl
  have iγ : (Scheme.Modules.pullback (baseChangeSnd c ψ)).obj (Dγ.pullbackAlong t (Category.comp_id t)).idealModule ≅
      (Dγ.pullbackAlong (ψ1 ≫ t) (Category.comp_id _)).idealModule := by
    haveI := Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison (baseChangeSnd c ψ)
      ((Dγ.pullbackAlong t (Category.comp_id t)).isInvertible_I_of_supportedIn U (hDγ.pullbackAlong _ _))
      (hI ▸ (Dγ.pullbackAlong (ψ1 ≫ t) (Category.comp_id _)).isInvertible_I_of_supportedIn U (hDγ.pullbackAlong _ _))
    exact asIso ((Dγ.pullbackAlong t (Category.comp_id t)).I.pullbackModuleComparison (baseChangeSnd c ψ)) ≪≫
      eqToIso (congrArg Scheme.IdealSheafData.module hI).symm

  have iE := (RelEffCartierDiv.nonempty_pullback_lineBundle_pullbackAlong_iso_of_supportedIn R c U E hEU ψ).some
  exact ⟨(Iso.refl _ ⊗ᵢ (iE.symm ⊗ᵢ iγ.symm)) ≪≫
      (Iso.refl _ ⊗ᵢ (Scheme.Modules.pullbackTensorObjIso (baseChangeSnd c ψ) _ _).symm) ≪≫
      (Scheme.Modules.pullbackTensorObjIso (baseChangeSnd c ψ) _ _).symm⟩

include hEU hDγ in

theorem nonempty_fibreModule_iso :
    Nonempty (fibreModule c t (s' ≫ ψ1)
        (L.L ⊗ ((E.pullbackAlong t (Category.comp_id t)).lineBundle ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)) ≅
      (Scheme.Modules.pullback (fibreIso R c t ψ1 s').hom).obj (fibreModule c (ψ1 ≫ t) s'
        ((L.pullbackAlong (⟨ψ1, rfl⟩ : SchemeHomOver (ψ1 ≫ t) t)).L ⊗
          ((E.pullbackAlong (ψ1 ≫ t) (Category.comp_id _)).lineBundle ⊗ (Dγ.pullbackAlong (ψ1 ≫ t) (Category.comp_id _)).idealModule)))) := by
  obtain ⟨iM⟩ := nonempty_Mγ_iso_pullback R c ε U E hEU Dγ hDγ t ψ1 L
  exact ⟨((Scheme.Modules.pullbackCongr (fibreIso_hom_fst_baseChangeSnd R c t ψ1 s')).app _).symm ≪≫
    ((Scheme.Modules.pullbackComp (fibreIso R c t ψ1 s').hom
      (pullback.fst (pullback.snd c (ψ1 ≫ t)) s' ≫ baseChangeSnd c (⟨ψ1, rfl⟩ : SchemeHomOver (ψ1 ≫ t) t))).app _).symm ≪≫
    (Scheme.Modules.pullback (fibreIso R c t ψ1 s').hom).mapIso
      (((Scheme.Modules.pullbackComp (pullback.fst (pullback.snd c (ψ1 ≫ t)) s')
        (baseChangeSnd c (⟨ψ1, rfl⟩ : SchemeHomOver (ψ1 ≫ t) t))).app _).symm ≪≫
        (Scheme.Modules.pullback _).mapIso iM.symm)⟩

include hEU hDγ in

theorem fibre_transport_to_t' (𝒲 : (pullback (pullback.snd c t) (s' ≫ ψ1)).TwoAffineOpenCover) :
    ∃ 𝒱 : (pullback (pullback.snd c (ψ1 ≫ t)) s').TwoAffineOpenCover,
      Nonempty ((𝒱.sectionsOf (fibreAt c (ψ1 ≫ t) s') (fibreModule c (ψ1 ≫ t) s'
          ((L.pullbackAlong (⟨ψ1, rfl⟩ : SchemeHomOver (ψ1 ≫ t) t)).L ⊗
            ((E.pullbackAlong (ψ1 ≫ t) (Category.comp_id _)).lineBundle ⊗ (Dγ.pullbackAlong (ψ1 ≫ t) (Category.comp_id _)).idealModule)))).H0 ≃ₗ[k]
        (𝒲.sectionsOf (fibreAt c t (s' ≫ ψ1)) (fibreModule c t (s' ≫ ψ1)
          (L.L ⊗ ((E.pullbackAlong t (Category.comp_id t)).lineBundle ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))).H0) ∧
      Nonempty ((𝒱.sectionsOf (fibreAt c (ψ1 ≫ t) s') (fibreModule c (ψ1 ≫ t) s'
          ((L.pullbackAlong (⟨ψ1, rfl⟩ : SchemeHomOver (ψ1 ≫ t) t)).L ⊗
            ((E.pullbackAlong (ψ1 ≫ t) (Category.comp_id _)).lineBundle ⊗ (Dγ.pullbackAlong (ψ1 ≫ t) (Category.comp_id _)).idealModule)))).H1 ≃ₗ[k]
        (𝒲.sectionsOf (fibreAt c t (s' ≫ ψ1)) (fibreModule c t (s' ≫ ψ1)
          (L.L ⊗ ((E.pullbackAlong t (Category.comp_id t)).lineBundle ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))).H1) := by
  obtain ⟨eφ⟩ := nonempty_fibreModule_iso R c ε U E hEU Dγ hDγ t ψ1 L s'

  let φ := fibreIso R c t ψ1 s'
  have hφ' : φ.symm.hom ≫ fibreAt c t (s' ≫ ψ1) = fibreAt c (ψ1 ≫ t) s' := by
    rw [Iso.symm_hom, Iso.inv_comp_eq, fibreIso_hom_fibreAt]
  have e' := ((Scheme.Modules.pullbackId _).app _).symm ≪≫
    ((Scheme.Modules.pullbackCongr φ.inv_hom_id).app _).symm ≪≫
    ((Scheme.Modules.pullbackComp φ.inv φ.hom).app _).symm ≪≫
    (Scheme.Modules.pullback φ.inv).mapIso eφ.symm
  obtain ⟨𝒱, -, -, h0, h1⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (fibreAt c (ψ1 ≫ t) s') (fibreAt c t (s' ≫ ψ1)) φ.symm hφ' 𝒲 _ _ e'
  exact ⟨𝒱, h0, h1⟩

include hEU hDγ in

theorem fin_transport {k : Type u} [Field k] [IsAlgClosed k] (x' : Spec (CommRingCat.of k) ⟶ T')
    (hfin : ∀ (σ : 𝟙_ (pullback c (x' ≫ (ψ1 ≫ t))).Modules ⟶ (Scheme.Modules.pullback (mapOnProdOver c x' rfl)).obj
        ((L.pullbackAlong (⟨ψ1, rfl⟩ : SchemeHomOver (ψ1 ≫ t) t)).L ⊗
          ((E.pullbackAlong (ψ1 ≫ t) (Category.comp_id _)).lineBundle ⊗ (Dγ.pullbackAlong (ψ1 ≫ t) (Category.comp_id _)).idealModule))),
      σ ≠ 0 → ((Scheme.Modules.zeroSchemeIdeal σ).support : Set ↥(pullback c (x' ≫ (ψ1 ≫ t)))) ⊆
        ((pullback.fst c (x' ≫ (ψ1 ≫ t))) ⁻¹ᵁ U : Set ↥(pullback c (x' ≫ (ψ1 ≫ t)))))
    (σ : 𝟙_ (pullback c ((x' ≫ ψ1) ≫ t)).Modules ⟶ (Scheme.Modules.pullback (mapOnProdOver c (x' ≫ ψ1) rfl)).obj
        (L.L ⊗ ((E.pullbackAlong t (Category.comp_id t)).lineBundle ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))
    (hσ : σ ≠ 0) :
    ((Scheme.Modules.zeroSchemeIdeal σ).support : Set ↥(pullback c ((x' ≫ ψ1) ≫ t))) ⊆
      ((pullback.fst c ((x' ≫ ψ1) ≫ t)) ⁻¹ᵁ U : Set ↥(pullback c ((x' ≫ ψ1) ≫ t))) :=
  (AlgebraicGeometry.RelPicard.FinTransport.finerAt_transport c U t (ψ1 ≫ t) (⟨ψ1, rfl⟩ : SchemeHomOver (ψ1 ≫ t) t)
      _ (isInvertible_Mγ R c ε U E hEU t L (Dγ.pullbackAlong t (Category.comp_id t)) (hDγ.pullbackAlong _ _)) _
      (nonempty_Mγ_iso_pullback R c ε U E hEU Dγ hDγ t ψ1 L).some x').1 hfin σ hσ

end Transport
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_relEffCartierDiv_eq_pullbackAlong_of_rigidify_iso_of_supportedIn_of_support_subset.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_relEffCartierDiv_eq_pullbackAlong_of_rigidify_iso_of_supportedIn_of_support_subset.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_relEffCartierDiv_eq_pullbackAlong_of_rigidify_iso_of_supportedIn_of_support_subset.AlgebraicGeometry.RelPicard.FinTransport"

end AlgebraicGeometry.RelPicard.K5bSupplyE
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_relEffCartierDiv_eq_pullbackAlong_of_rigidify_iso_of_supportedIn_of_support_subset.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_relEffCartierDiv_eq_pullbackAlong_of_rigidify_iso_of_supportedIn_of_support_subset.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_relEffCartierDiv_eq_pullbackAlong_of_rigidify_iso_of_supportedIn_of_support_subset.AlgebraicGeometry.RelPicard.FinTransport"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_relEffCartierDiv_eq_pullbackAlong_of_rigidify_iso_of_supportedIn_of_support_subset.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_relEffCartierDiv_eq_pullbackAlong_of_rigidify_iso_of_supportedIn_of_support_subset.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_relEffCartierDiv_eq_pullbackAlong_of_rigidify_iso_of_supportedIn_of_support_subset.AlgebraicGeometry.RelPicard.FinTransport"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_relEffCartierDiv_eq_pullbackAlong_of_rigidify_iso_of_supportedIn_of_support_subset.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_relEffCartierDiv_eq_pullbackAlong_of_rigidify_iso_of_supportedIn_of_support_subset.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_relEffCartierDiv_eq_pullbackAlong_of_rigidify_iso_of_supportedIn_of_support_subset.AlgebraicGeometry.RelPicard.FinTransport"

open CategoryTheory CategoryTheory.Limits Opposite _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_RelPicard_relEffCartierDiv_eq_pullbackAlong_of_rigidify_iso_of_supportedIn_of_support_subset.AlgebraicGeometry _root_.AlgebraicGeometry.RelPicard _root_.P2MW.S_AlgebraicGeometry_RelPicard_relEffCartierDiv_eq_pullbackAlong_of_rigidify_iso_of_supportedIn_of_support_subset.AlgebraicGeometry.RelPicard NeronModelInfra AlgebraicGeometry.RelPicard.K5bSupplyE in

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (g e ρ : ℕ) (hr : g + e = ρ)

    (E : RelEffCartierDiv c ρ (𝟙 (Spec (CommRingCat.of R)))) (hEU : E.SupportedIn U)
    (Dγ : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R)))) (hDγ : Dγ.SupportedIn U)
    (hsect : ∀ ⦃V : Scheme.{u}⦄ (u : V ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType u] (M : (pullback c u).Modules),
      Scheme.Modules.IsInvertible M →
      (∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ V) (𝒲 : (pullback (pullback.snd c u) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c u s) (fibreModule c u s M)).H1 ∧
          Module.finrank k (𝒲.sectionsOf (fibreAt c u s) (fibreModule c u s M)).H0 = 1) →
      (∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ V)
        (σ : 𝟙_ (pullback c (x ≫ u)).Modules ⟶ (Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj M), σ ≠ 0 →
        ∃ Dx : RelEffCartierDiv c g (x ≫ u), Dx.I = Scheme.Modules.zeroSchemeIdeal σ ∧ Dx.SupportedIn U) →
      ∃ (D₀ : RelEffCartierDiv c g u) (N : V.Modules), Scheme.Modules.IsInvertible N ∧
        Nonempty (D₀.lineBundle ≅ M ⊗ (Scheme.Modules.pullback (pullback.snd c u)).obj N) ∧
        ∀ (d' : ℕ) (D' : RelEffCartierDiv c d' u) (N' : V.Modules), Scheme.Modules.IsInvertible N' → D'.SupportedIn U →
          Nonempty (D'.lineBundle ≅ M ⊗ (Scheme.Modules.pullback (pullback.snd c u)).obj N') → D'.I = D₀.I)

    (hZfibγ : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
      (L : RigidifiedLineBundle c ε t), FibrewiseAlgEquivZero L →
      ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ T)
        (σ : 𝟙_ (pullback c (x ≫ t)).Modules ⟶ (Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj
          (L.L ⊗ ((E.pullbackAlong t (Category.comp_id t)).lineBundle ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule))), σ ≠ 0 →

        ((Scheme.Modules.zeroSchemeIdeal σ).support : Set ↥(pullback c (x ≫ t))) ⊆ ((pullback.fst c (x ≫ t)) ⁻¹ᵁ U : Set ↥(pullback c (x ≫ t))) →
        ∃ Dx : RelEffCartierDiv c g (x ≫ t), Dx.I = Scheme.Modules.zeroSchemeIdeal σ ∧ Dx.SupportedIn U)
    (hH0one : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) (L : RigidifiedLineBundle c ε t), FibrewiseAlgEquivZero L →
      ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T) (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ ((E.pullbackAlong t (Category.comp_id t)).lineBundle ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))).H1 →
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ ((E.pullbackAlong t (Category.comp_id t)).lineBundle ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))).H0 = 1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (L : RigidifiedLineBundle c ε t) (hL : FibrewiseAlgEquivZero L) (W : T.Opens)

    (hWmax : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
      (∀ (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ ((E.pullbackAlong t (Category.comp_id t)).lineBundle ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))).H1) →
      (∀ (σ : 𝟙_ (pullback c (s ≫ t)).Modules ⟶ (Scheme.Modules.pullback (mapOnProdOver c s rfl)).obj
          (L.L ⊗ ((E.pullbackAlong t (Category.comp_id t)).lineBundle ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule))),
        σ ≠ 0 → ((Scheme.Modules.zeroSchemeIdeal σ).support : Set ↥(pullback c (s ≫ t))) ⊆ ((pullback.fst c (s ≫ t)) ⁻¹ᵁ U : Set ↥(pullback c (s ≫ t)))) →
      Set.range ⇑s ⊆ (W : Set T))
    (D : RelEffCartierDiv c ρ (W.ι ≫ t)) (D₀ : RelEffCartierDiv c g (W.ι ≫ t))
    (hD : D.I = D₀.I * (Dγ.pullbackAlong (W.ι ≫ t) (Category.comp_id _)).I) (hD₀U : D₀.SupportedIn U)
    (hDL : Nonempty (Scheme.Modules.rigidify (RelPicard.rigSection c (W.ι ≫ t) ε) (pullback.snd c (W.ι ≫ t))
        (D.lineBundle ⊗ (E.pullbackAlong (W.ι ≫ t) (Category.comp_id _)).idealModule) ≅
      (L.pullbackAlong (⟨W.ι, rfl⟩ : SchemeHomOver (W.ι ≫ t) t)).L))
    {T' : Scheme.{u}} (t' : T' ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t'] (ψ : SchemeHomOver t' t)
    (D' : RelEffCartierDiv c ρ t') (D₀' : RelEffCartierDiv c g t')
    (hD' : D'.I = D₀'.I * (Dγ.pullbackAlong t' (Category.comp_id _)).I) (hD₀'U : D₀'.SupportedIn U)
    (hD'L : Nonempty (Scheme.Modules.rigidify (RelPicard.rigSection c t' ε) (pullback.snd c t')
        (D'.lineBundle ⊗ (E.pullbackAlong t' (Category.comp_id _)).idealModule) ≅ (L.pullbackAlong ψ).L))
    (h1' : ∀ (k : Type u) [Field k] (s' : Spec (CommRingCat.of k) ⟶ T')
      (𝒲 : (pullback (pullback.snd c t') s').TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t' s') (fibreModule c t' s'
          ((L.pullbackAlong ψ).L ⊗ ((E.pullbackAlong t' (Category.comp_id t')).lineBundle ⊗ (Dγ.pullbackAlong t' (Category.comp_id t')).idealModule)))).H1)

    (hfin' : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ T')
      (σ : 𝟙_ (pullback c (x ≫ t')).Modules ⟶ (Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj
        ((L.pullbackAlong ψ).L ⊗ ((E.pullbackAlong t' (Category.comp_id t')).lineBundle ⊗ (Dγ.pullbackAlong t' (Category.comp_id t')).idealModule))),
      σ ≠ 0 → ((Scheme.Modules.zeroSchemeIdeal σ).support : Set ↥(pullback c (x ≫ t'))) ⊆ ((pullback.fst c (x ≫ t')) ⁻¹ᵁ U : Set ↥(pullback c (x ≫ t')))) :
    Set.range ⇑ψ.1 ⊆ (W : Set T) ∧
      ∀ (φ : T' ⟶ W) (hφ : φ ≫ W.ι = ψ.1),
        D' = D.pullbackAlong φ (by rw [← Category.assoc, hφ]; exact ψ.2) := by
  obtain ⟨ψ1, rfl⟩ := ψ
  subst hr

  set Lψ := L.pullbackAlong (⟨ψ1, rfl⟩ : SchemeHomOver (ψ1 ≫ t) t) with hLψ
  set DγT' := Dγ.pullbackAlong (ψ1 ≫ t) (Category.comp_id _) with hDγT'def
  have hDγT' : DγT'.SupportedIn U := hDγ.pullbackAlong (ψ1 ≫ t) (Category.comp_id _)

  have hL' : FibrewiseAlgEquivZero Lψ := hL.pullback _
  have hfib' : ∀ (k : Type u) [Field k] (s' : Spec (CommRingCat.of k) ⟶ T')
      (𝒲 : (pullback (pullback.snd c (ψ1 ≫ t)) s').TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c (ψ1 ≫ t) s') (fibreModule c (ψ1 ≫ t) s'
        (Lψ.L ⊗ ((E.pullbackAlong (ψ1 ≫ t) (Category.comp_id _)).lineBundle ⊗ DγT'.idealModule)))).H1 ∧
      Module.finrank k (𝒲.sectionsOf (fibreAt c (ψ1 ≫ t) s') (fibreModule c (ψ1 ≫ t) s'
        (Lψ.L ⊗ ((E.pullbackAlong (ψ1 ≫ t) (Category.comp_id _)).lineBundle ⊗ DγT'.idealModule)))).H0 = 1 :=
    fun k _ s' 𝒲 => ⟨h1' k s' 𝒲, hH0one (ψ1 ≫ t) Lψ hL' k s' 𝒲 (h1' k s' 𝒲)⟩
  refine ⟨?_, ?_⟩
  ·
    rintro _ ⟨y, rfl⟩
    classical
    let κ := T'.residueField y
    let kb : Type u := AlgebraicClosure κ
    set sb : Spec (CommRingCat.of kb) ⟶ T' :=
      Spec.map (CommRingCat.ofHom (algebraMap κ kb)) ≫ T'.fromSpecResidueField y with hsbdef
    have hsb : sb (IsLocalRing.closedPoint kb) = y := by
      change (T'.fromSpecResidueField y) (Spec.map (CommRingCat.ofHom (algebraMap κ kb)) (IsLocalRing.closedPoint kb)) = y
      rw [show (Spec.map (CommRingCat.ofHom (algebraMap κ kb))) (IsLocalRing.closedPoint kb) = IsLocalRing.closedPoint κ from
        Subsingleton.elim _ _, Scheme.fromSpecResidueField_apply]
    have key := hWmax kb (sb ≫ ψ1)
      (fun 𝒲 => by
        obtain ⟨𝒱, -, ⟨e1⟩⟩ := fibre_transport_to_t' R c ε U E hEU Dγ hDγ t ψ1 L sb 𝒲
        haveI := h1' _ sb 𝒱
        exact e1.symm.toEquiv.subsingleton)
      (fun σ hσ => fin_transport R c ε U E hEU Dγ hDγ t ψ1 L sb (hfin' kb sb) σ hσ)
    exact key ⟨IsLocalRing.closedPoint kb, by rw [Scheme.Hom.comp_apply, hsb]⟩
  ·
    intro φ hφ
    have hφt : φ ≫ (W.ι ≫ t) = ψ1 ≫ t := by rw [← Category.assoc, hφ]
    have hDU : D.SupportedIn U := by
      intro x hx
      rw [hD] at hx
      change x ∈ ((D₀.I * (Dγ.pullbackAlong (W.ι ≫ t) (Category.comp_id _)).I).support : Set _) at hx
      rw [Scheme.IdealSheafData.support_mul, TopologicalSpace.Closeds.coe_sup] at hx
      exact hx.elim (fun h => hD₀U h) (fun h => (hDγ.pullbackAlong (W.ι ≫ t) (Category.comp_id _)) h)

    have hM' : Scheme.Modules.IsInvertible (Lψ.L ⊗ ((E.pullbackAlong (ψ1 ≫ t) (Category.comp_id _)).lineBundle ⊗ DγT'.idealModule)) :=
      isInvertible_Mγ R c ε U E hEU (ψ1 ≫ t) Lψ DγT' hDγT'

    obtain ⟨N₁, hN₁, ⟨e₁⟩⟩ := exists_lineBundle_iso_of_rigidify_iso R c ε U E hEU (ψ1 ≫ t) Lψ DγT' hDγT' D₀' hD₀'U D' hD' hD'L

    have hD₂ : (D.pullbackAlong φ hφt).I = (D₀.pullbackAlong φ hφt).I * DγT'.I := by
      rw [pullbackAlong_I_eq_mul D D₀ _ hD φ hφt, hDγT'def, RelEffCartierDiv.pullbackAlong_comp]
      congr 2
      refine RelEffCartierDiv.ext ?_
      change Dγ.I.comap _ = Dγ.I.comap _
      congr 1
      simp only [hφ, ← Category.assoc]
    have hβcomp : baseChangeSnd c (⟨φ, hφt⟩ : SchemeHomOver (ψ1 ≫ t) (W.ι ≫ t)) ≫
        baseChangeSnd c (⟨W.ι, rfl⟩ : SchemeHomOver (W.ι ≫ t) t) =
          baseChangeSnd c (⟨ψ1, rfl⟩ : SchemeHomOver (ψ1 ≫ t) t) := by
      apply pullback.hom_ext
      · simp only [RelPicard.baseChangeSnd, Category.assoc, pullback.lift_fst, Category.comp_id]
      · simp only [RelPicard.baseChangeSnd, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, hφ]
    have eL : (Scheme.Modules.pullback (baseChangeSnd c (⟨φ, hφt⟩ : SchemeHomOver (ψ1 ≫ t) (W.ι ≫ t)))).obj
        (L.pullbackAlong (⟨W.ι, rfl⟩ : SchemeHomOver (W.ι ≫ t) t)).L ≅ Lψ.L :=
      (Scheme.Modules.pullbackComp _ _).app L.L ≪≫ (Scheme.Modules.pullbackCongr hβcomp).app L.L
    have hDL₂ : Nonempty (Scheme.Modules.rigidify (rigSection c (ψ1 ≫ t) ε) (pullback.snd c (ψ1 ≫ t))
        ((D.pullbackAlong φ hφt).lineBundle ⊗ (E.pullbackAlong (ψ1 ≫ t) (Category.comp_id _)).idealModule) ≅ Lψ.L) := by
      obtain ⟨i⟩ := RelEffCartierDiv.nonempty_rigidify_lineBundle_tensor_idealModule_pullbackAlong_iso_pullback_of_supportedIn
        c ε U E hEU (⟨φ, hφt⟩ : SchemeHomOver (ψ1 ≫ t) (W.ι ≫ t)) D hDU
      exact ⟨i ≪≫ (Scheme.Modules.pullback _).mapIso hDL.some ≪≫ eL⟩
    obtain ⟨N₂, hN₂, ⟨e₂⟩⟩ := exists_lineBundle_iso_of_rigidify_iso R c ε U E hEU (ψ1 ≫ t) Lψ DγT' hDγT'
      (D₀.pullbackAlong φ hφt) (hD₀U.pullbackAlong φ hφt) (D.pullbackAlong φ hφt) hD₂ hDL₂

    obtain ⟨D₀'', N'', -, -, huq⟩ := hsect (ψ1 ≫ t) _ hM' hfib'
      (fun k _ _ x σ hσ => hZfibγ (ψ1 ≫ t) Lψ hL' k x σ hσ (hfin' k x σ hσ))
    have huniq : D₀'.I = (D₀.pullbackAlong φ hφt).I :=
      (huq g D₀' N₁ hN₁ hD₀'U ⟨e₁⟩).trans (huq g (D₀.pullbackAlong φ hφt) N₂ hN₂ (hD₀U.pullbackAlong φ hφt) ⟨e₂⟩).symm

    refine RelEffCartierDiv.ext ?_
    rw [hD', hD₂, huniq]

end S_AlgebraicGeometry_RelPicard_relEffCartierDiv_eq_pullbackAlong_of_rigidify_iso_of_supportedIn_of_support_subset
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_relEffCartierDiv_eq_pullbackAlong_of_rigidify_iso_of_supportedIn_of_support_subset (solution)
