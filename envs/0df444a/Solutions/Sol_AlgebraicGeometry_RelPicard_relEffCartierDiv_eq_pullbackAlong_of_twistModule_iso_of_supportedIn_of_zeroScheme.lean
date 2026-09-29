-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.relEffCartierDiv_eq_pullbackAlong_of_twistModule_iso_of_supportedIn_of_zeroScheme
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/5a8d8cea-a59d-5a52-8299-53b8a6bfa7b4

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivTwist2
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModuleMaps
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_pullback_sectionTwist_iso_of_range_subset
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isIso_pullbackModuleComparison
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I_of_supportedIn
import Theorems.Thm_AlgebraicGeometry_RelPicard_isInvertible_sectionIdeal_of_range_subset
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_rigidify_pullback_tensor_iso

import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_nonempty_twistModule_pullbackAlong_iso_pullback_of_supportedIn
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_mul
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_relEffCartierDiv_eq_pullbackAlong_of_twistModule_iso_of_supportedIn_of_zeroScheme
p2m_attr_erase "instance" "AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap"
p2m_attr_erase "simp" "AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst"

set_option autoImplicit false

universe u

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "SmoothOfRelativeDimension IsProper Scheme.Modules.pullback Scheme.Hom LocallyOfFiniteType Spec Scheme IsSeparated Scheme.Modules.pullbackCongr Scheme.fromSpecResidueField_apply Scheme.Modules.pullbackId Scheme.IdealSheafData.support_mul Scheme.Modules Scheme.Hom.comp_apply Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible RelPicard.baseChangeSnd Scheme.Modules.dual Scheme.IdealSheafData.module Scheme.IdealSheafData.invModule RelEffCartierDiv RelEffCartierDiv.ext mapOnProdOver RelEffCartierDiv.pullbackAlong_comp Scheme.TwoAffineOpenCover RelEffCartierDiv.twistModule_def Scheme.Modules.rigidify_def Scheme.Modules.pullbackTensorObjIso Scheme.Modules.pullbackTensorUnitObjIso Scheme.Modules.zeroSchemeIdeal Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison Scheme.IdealSheafData.IsInvertible RelEffCartierDiv.nonempty_twistModule_pullbackAlong_iso_pullback_of_supportedIn Scheme.IdealSheafData.comap_mul"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd rigSection RigidifiedLineBundle fibreAt FibrewiseAlgEquivZero sectionIdeal sectionTwist fibreModule nonempty_pullback_sectionTwist_iso_of_range_subset isInvertible_sectionIdeal_of_range_subset"
namespace K5bSupply
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_relEffCartierDiv_eq_pullbackAlong_of_twistModule_iso_of_supportedIn_of_zeroScheme.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_relEffCartierDiv_eq_pullbackAlong_of_twistModule_iso_of_supportedIn_of_zeroScheme.AlgebraicGeometry.RelPicard NeronModelInfra"

variable (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsSeparated c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)] (hεU : Set.range ε.1 ⊆ (U : Set C))

include hεU in
theorem isInvertible_sectionIdeal {V : Scheme.{u}} (u : V ⟶ Spec (CommRingCat.of R)) :
    (sectionIdeal c ε u).IsInvertible :=
  isInvertible_sectionIdeal_of_range_subset c ε U hεU u

include hεU in
theorem isInvertible_sectionTwist {V : Scheme.{u}} (u : V ⟶ Spec (CommRingCat.of R)) (n : ℕ) :
    Scheme.Modules.IsInvertible (sectionTwist c ε u n) :=
  ((isInvertible_sectionIdeal R c ε U hεU u).pow n).isInvertible_invModule

include hεU in
theorem isInvertible_Mγ {e n : ℕ} {V : Scheme.{u}} (u : V ⟶ Spec (CommRingCat.of R))
    (LV : RigidifiedLineBundle c ε u) (DγV : RelEffCartierDiv c e u) (hDγV : DγV.SupportedIn U) :
    Scheme.Modules.IsInvertible (LV.L ⊗ (sectionTwist c ε u n ⊗ DγV.idealModule)) :=
  LV.isInvertible.tensor ((isInvertible_sectionTwist R c ε U hεU u n).tensor (DγV.isInvertible_I_of_supportedIn U hDγV).isInvertible_module)

include hεU in

theorem exists_lineBundle_iso_of_twistModule_iso
    {g e : ℕ} {V : Scheme.{u}} (u : V ⟶ Spec (CommRingCat.of R))
    (LU : RigidifiedLineBundle c ε u) (DγU : RelEffCartierDiv c e u) (hDγU : DγU.SupportedIn U)
    (D₀ : RelEffCartierDiv c g u) (hD₀U : D₀.SupportedIn U) (D : RelEffCartierDiv c (g + e) u) (hD : D.I = D₀.I * DγU.I)
    (hDL : Nonempty (D.twistModule c ε ≅ LU.L)) :
    ∃ N : V.Modules, Scheme.Modules.IsInvertible N ∧
      Nonempty (D₀.lineBundle ≅ (LU.L ⊗ (sectionTwist c ε u (g + e) ⊗ DγU.idealModule)) ⊗
        (Scheme.Modules.pullback (pullback.snd c u)).obj N) := by
  have hsIr : ((sectionIdeal c ε u) ^ (g + e)).IsInvertible := (isInvertible_sectionIdeal R c ε U hεU u).pow _
  have hD₀ : D₀.I.IsInvertible := D₀.isInvertible_I_of_supportedIn U hD₀U
  have hDγ : DγU.I.IsInvertible := DγU.isInvertible_I_of_supportedIn U hDγU
  have hDI : D.I.IsInvertible := by rw [hD]; exact hD₀.mul hDγ

  set F := ((sectionIdeal c ε u) ^ (g + e)).module with hF
  set X := D.lineBundle ⊗ F with hX
  have hXinv : Scheme.Modules.IsInvertible X := hDI.isInvertible_invModule.tensor hsIr.isInvertible_module
  set N₀ : V.Modules := Scheme.Modules.dual ((Scheme.Modules.pullback (rigSection c u ε)).obj X) with hN₀
  have hN₀ : Scheme.Modules.IsInvertible N₀ := (hXinv.pullback _).dual.1

  refine ⟨Scheme.Modules.dual N₀, hN₀.dual.1, ?_⟩
  have cN : (Scheme.Modules.pullback (pullback.snd c u)).obj N₀ ⊗
      (Scheme.Modules.pullback (pullback.snd c u)).obj (Scheme.Modules.dual N₀) ≅ 𝟙_ _ :=
    (Scheme.Modules.pullbackTensorObjIso (pullback.snd c u) _ _).symm ≪≫
      (Scheme.Modules.pullback _).mapIso hN₀.dual.2.some ≪≫ Scheme.Modules.pullbackTensorUnitObjIso _

  have j0 : X ⊗ (Scheme.Modules.pullback (pullback.snd c u)).obj N₀ ≅ LU.L := by
    have h := hDL.some
    rw [RelEffCartierDiv.twistModule_def, Scheme.Modules.rigidify_def] at h
    exact h

  have j1 : X ≅ LU.L ⊗ (Scheme.Modules.pullback (pullback.snd c u)).obj (Scheme.Modules.dual N₀) :=
    (ρ_ X).symm ≪≫ (Iso.refl X ⊗ᵢ cN.symm) ≪≫ (α_ _ _ _).symm ≪≫ (j0 ⊗ᵢ Iso.refl _)

  have cST : F ⊗ sectionTwist c ε u (g + e) ≅ 𝟙_ _ := by
    rw [hF]; exact (hsIr.isInvertible_module.dual).2.some
  have cγ : DγU.lineBundle ⊗ DγU.idealModule ≅ 𝟙_ _ :=
    (β_ _ _) ≪≫ (hDγ.isInvertible_module.dual).2.some

  have j2 : D.lineBundle ≅ (LU.L ⊗ (Scheme.Modules.pullback (pullback.snd c u)).obj (Scheme.Modules.dual N₀)) ⊗
      sectionTwist c ε u (g + e) :=
    (ρ_ _).symm ≪≫ (Iso.refl _ ⊗ᵢ cST.symm) ≪≫ (α_ _ _ _).symm ≪≫ ((show D.lineBundle ⊗ F ≅ _ from j1) ⊗ᵢ Iso.refl _)

  have i1 : D.lineBundle ≅ D₀.lineBundle ⊗ DγU.lineBundle :=
    eqToIso (congrArg Scheme.IdealSheafData.invModule hD) ≪≫ (hD₀.nonempty_mul_invModule_iso_tensor hDγ).some
  have j3 : D₀.lineBundle ≅ D.lineBundle ⊗ DγU.idealModule :=
    (ρ_ _).symm ≪≫ (Iso.refl _ ⊗ᵢ cγ.symm) ≪≫ (α_ _ _ _).symm ≪≫ (i1.symm ⊗ᵢ Iso.refl _)
  refine ⟨j3 ≪≫ (j2 ⊗ᵢ Iso.refl _) ≪≫ ?_⟩

  exact (α_ _ _ _) ≪≫ (α_ _ _ _) ≪≫ (Iso.refl _ ⊗ᵢ (β_ _ _)) ≪≫ (α_ _ _ _).symm

section Transport

variable {e : ℕ} (r : ℕ) (Dγ : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R)))) (hDγ : Dγ.SupportedIn U)
  {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (ψ1 : T' ⟶ T) (L : RigidifiedLineBundle c ε t)
  {k : Type u} [Field k] (s' : Spec (CommRingCat.of k) ⟶ T')

noncomputable def fibreIso : pullback (pullback.snd c t) (s' ≫ ψ1) ≅ pullback (pullback.snd c (ψ1 ≫ t)) s' :=
  pullbackLeftPullbackSndIso c t (s' ≫ ψ1) ≪≫ pullback.congrHom rfl (Category.assoc s' ψ1 t) ≪≫
    (pullbackLeftPullbackSndIso c (ψ1 ≫ t) s').symm

theorem fibreIso_hom_fibreAt :
    (fibreIso R c t ψ1 s').hom ≫ fibreAt c (ψ1 ≫ t) s' = fibreAt c t (s' ≫ ψ1) := by
  simp only [fibreIso, fibreAt, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    pullbackLeftPullbackSndIso_inv_snd_snd, pullback.congrHom_hom, pullback.lift_snd,
    Category.comp_id, pullbackLeftPullbackSndIso_hom_snd]

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

include hεU hDγ in

theorem nonempty_Mγ_iso_pullback :
    Nonempty ((L.pullbackAlong (⟨ψ1, rfl⟩ : SchemeHomOver (ψ1 ≫ t) t)).L ⊗
        (sectionTwist c ε (ψ1 ≫ t) r ⊗ (Dγ.pullbackAlong (ψ1 ≫ t) (Category.comp_id _)).idealModule) ≅
      (Scheme.Modules.pullback (baseChangeSnd c (⟨ψ1, rfl⟩ : SchemeHomOver (ψ1 ≫ t) t))).obj
        (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule))) := by
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
  exact ⟨(Iso.refl _ ⊗ᵢ ((nonempty_pullback_sectionTwist_iso_of_range_subset R c ε U hεU ψ r).some.symm ⊗ᵢ iγ.symm)) ≪≫
      (Iso.refl _ ⊗ᵢ (Scheme.Modules.pullbackTensorObjIso (baseChangeSnd c ψ) _ _).symm) ≪≫
      (Scheme.Modules.pullbackTensorObjIso (baseChangeSnd c ψ) _ _).symm⟩

include hεU hDγ in

theorem nonempty_fibreModule_iso :
    Nonempty (fibreModule c t (s' ≫ ψ1)
        (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)) ≅
      (Scheme.Modules.pullback (fibreIso R c t ψ1 s').hom).obj (fibreModule c (ψ1 ≫ t) s'
        ((L.pullbackAlong (⟨ψ1, rfl⟩ : SchemeHomOver (ψ1 ≫ t) t)).L ⊗
          (sectionTwist c ε (ψ1 ≫ t) r ⊗ (Dγ.pullbackAlong (ψ1 ≫ t) (Category.comp_id _)).idealModule)))) := by
  obtain ⟨iM⟩ := nonempty_Mγ_iso_pullback R c ε U hεU r Dγ hDγ t ψ1 L
  exact ⟨((Scheme.Modules.pullbackCongr (fibreIso_hom_fst_baseChangeSnd R c t ψ1 s')).app _).symm ≪≫
    ((Scheme.Modules.pullbackComp (fibreIso R c t ψ1 s').hom
      (pullback.fst (pullback.snd c (ψ1 ≫ t)) s' ≫ baseChangeSnd c (⟨ψ1, rfl⟩ : SchemeHomOver (ψ1 ≫ t) t))).app _).symm ≪≫
    (Scheme.Modules.pullback (fibreIso R c t ψ1 s').hom).mapIso
      (((Scheme.Modules.pullbackComp (pullback.fst (pullback.snd c (ψ1 ≫ t)) s')
        (baseChangeSnd c (⟨ψ1, rfl⟩ : SchemeHomOver (ψ1 ≫ t) t))).app _).symm ≪≫
        (Scheme.Modules.pullback _).mapIso iM.symm)⟩

include hεU hDγ in

theorem fibre_transport_to_t (𝒲 : (pullback (pullback.snd c (ψ1 ≫ t)) s').TwoAffineOpenCover) :
    ∃ 𝒱 : (pullback (pullback.snd c t) (s' ≫ ψ1)).TwoAffineOpenCover,
      Nonempty ((𝒱.sectionsOf (fibreAt c t (s' ≫ ψ1)) (fibreModule c t (s' ≫ ψ1)
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))).H0 ≃ₗ[k]
        (𝒲.sectionsOf (fibreAt c (ψ1 ≫ t) s') (fibreModule c (ψ1 ≫ t) s'
          ((L.pullbackAlong (⟨ψ1, rfl⟩ : SchemeHomOver (ψ1 ≫ t) t)).L ⊗
            (sectionTwist c ε (ψ1 ≫ t) r ⊗ (Dγ.pullbackAlong (ψ1 ≫ t) (Category.comp_id _)).idealModule)))).H0) ∧
      Nonempty ((𝒱.sectionsOf (fibreAt c t (s' ≫ ψ1)) (fibreModule c t (s' ≫ ψ1)
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))).H1 ≃ₗ[k]
        (𝒲.sectionsOf (fibreAt c (ψ1 ≫ t) s') (fibreModule c (ψ1 ≫ t) s'
          ((L.pullbackAlong (⟨ψ1, rfl⟩ : SchemeHomOver (ψ1 ≫ t) t)).L ⊗
            (sectionTwist c ε (ψ1 ≫ t) r ⊗ (Dγ.pullbackAlong (ψ1 ≫ t) (Category.comp_id _)).idealModule)))).H1) := by
  obtain ⟨eφ⟩ := nonempty_fibreModule_iso R c ε U hεU r Dγ hDγ t ψ1 L s'
  obtain ⟨𝒱, -, -, h0, h1⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (fibreAt c t (s' ≫ ψ1)) (fibreAt c (ψ1 ≫ t) s') (fibreIso R c t ψ1 s') (fibreIso_hom_fibreAt R c t ψ1 s') 𝒲 _ _ eφ
  exact ⟨𝒱, h0, h1⟩

include hεU hDγ in

theorem fibre_transport_to_t' (𝒲 : (pullback (pullback.snd c t) (s' ≫ ψ1)).TwoAffineOpenCover) :
    ∃ 𝒱 : (pullback (pullback.snd c (ψ1 ≫ t)) s').TwoAffineOpenCover,
      Nonempty ((𝒱.sectionsOf (fibreAt c (ψ1 ≫ t) s') (fibreModule c (ψ1 ≫ t) s'
          ((L.pullbackAlong (⟨ψ1, rfl⟩ : SchemeHomOver (ψ1 ≫ t) t)).L ⊗
            (sectionTwist c ε (ψ1 ≫ t) r ⊗ (Dγ.pullbackAlong (ψ1 ≫ t) (Category.comp_id _)).idealModule)))).H0 ≃ₗ[k]
        (𝒲.sectionsOf (fibreAt c t (s' ≫ ψ1)) (fibreModule c t (s' ≫ ψ1)
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))).H0) ∧
      Nonempty ((𝒱.sectionsOf (fibreAt c (ψ1 ≫ t) s') (fibreModule c (ψ1 ≫ t) s'
          ((L.pullbackAlong (⟨ψ1, rfl⟩ : SchemeHomOver (ψ1 ≫ t) t)).L ⊗
            (sectionTwist c ε (ψ1 ≫ t) r ⊗ (Dγ.pullbackAlong (ψ1 ≫ t) (Category.comp_id _)).idealModule)))).H1 ≃ₗ[k]
        (𝒲.sectionsOf (fibreAt c t (s' ≫ ψ1)) (fibreModule c t (s' ≫ ψ1)
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))).H1) := by
  obtain ⟨eφ⟩ := nonempty_fibreModule_iso R c ε U hεU r Dγ hDγ t ψ1 L s'

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

end Transport

end AlgebraicGeometry.RelPicard.K5bSupply

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "SmoothOfRelativeDimension IsProper Scheme.Modules.pullback Scheme.Hom LocallyOfFiniteType Spec Scheme IsSeparated Scheme.Modules.pullbackCongr Scheme.fromSpecResidueField_apply Scheme.Modules.pullbackId Scheme.IdealSheafData.support_mul Scheme.Modules Scheme.Hom.comp_apply Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible RelPicard.baseChangeSnd Scheme.Modules.dual Scheme.IdealSheafData.module Scheme.IdealSheafData.invModule RelEffCartierDiv RelEffCartierDiv.ext mapOnProdOver RelEffCartierDiv.pullbackAlong_comp Scheme.TwoAffineOpenCover RelEffCartierDiv.twistModule_def Scheme.Modules.rigidify_def Scheme.Modules.pullbackTensorObjIso Scheme.Modules.pullbackTensorUnitObjIso Scheme.Modules.zeroSchemeIdeal Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison Scheme.IdealSheafData.IsInvertible RelEffCartierDiv.nonempty_twistModule_pullbackAlong_iso_pullback_of_supportedIn Scheme.IdealSheafData.comap_mul"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd rigSection RigidifiedLineBundle fibreAt FibrewiseAlgEquivZero sectionIdeal sectionTwist fibreModule nonempty_pullback_sectionTwist_iso_of_range_subset isInvertible_sectionIdeal_of_range_subset"
namespace K5bUniv
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_relEffCartierDiv_eq_pullbackAlong_of_twistModule_iso_of_supportedIn_of_zeroScheme.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_relEffCartierDiv_eq_pullbackAlong_of_twistModule_iso_of_supportedIn_of_zeroScheme.AlgebraicGeometry.RelPicard NeronModelInfra P2MW.S_AlgebraicGeometry_RelPicard_relEffCartierDiv_eq_pullbackAlong_of_twistModule_iso_of_supportedIn_of_zeroScheme.AlgebraicGeometry.RelPicard.K5bSupply"

variable {R : Type u} [CommRing R]

theorem pullbackAlong_I_eq_mul {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {n m l : ℕ}
    {T' : Scheme.{u}} {g' : T' ⟶ S} (D : RelEffCartierDiv f n g') (D₀ : RelEffCartierDiv f m g') (E : RelEffCartierDiv f l g')
    (hD : D.I = D₀.I * E.I) {T : Scheme.{u}} {g : T ⟶ S} (φ : T ⟶ T') (hφ : φ ≫ g' = g) :
    (D.pullbackAlong φ hφ).I = (D₀.pullbackAlong φ hφ).I * (E.pullbackAlong φ hφ).I := by
  change D.I.comap _ = D₀.I.comap _ * E.I.comap _
  rw [hD, Scheme.IdealSheafData.comap_mul]

variable (R) [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)] (hεU : Set.range ε.1 ⊆ (U : Set C))

include hεU in
theorem UNIV'
    (g e r : ℕ) (hr : g + e = r) (Dγ : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R)))) (hDγ : Dγ.SupportedIn U)
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
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule))), σ ≠ 0 →
        ∃ Dx : RelEffCartierDiv c g (x ≫ t), Dx.I = Scheme.Modules.zeroSchemeIdeal σ ∧ Dx.SupportedIn U)
    (hH0one : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) (L : RigidifiedLineBundle c ε t), FibrewiseAlgEquivZero L →
      ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T) (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))).H1 →
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))).H0 = 1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (L : RigidifiedLineBundle c ε t) (hL : FibrewiseAlgEquivZero L) (W : T.Opens)
    (hWmax : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
      (∀ (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))).H1) → Set.range ⇑s ⊆ (W : Set T))
    (D : RelEffCartierDiv c r (W.ι ≫ t)) (D₀ : RelEffCartierDiv c g (W.ι ≫ t))
    (hD : D.I = D₀.I * (Dγ.pullbackAlong (W.ι ≫ t) (Category.comp_id _)).I) (hD₀U : D₀.SupportedIn U)
    (hDL : Nonempty (D.twistModule c ε ≅ (L.pullbackAlong (⟨W.ι, rfl⟩ : SchemeHomOver (W.ι ≫ t) t)).L))
    {T' : Scheme.{u}} (t' : T' ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t'] (ψ : SchemeHomOver t' t)
    (D' : RelEffCartierDiv c r t') (D₀' : RelEffCartierDiv c g t')
    (hD' : D'.I = D₀'.I * (Dγ.pullbackAlong t' (Category.comp_id _)).I) (hD₀'U : D₀'.SupportedIn U)
    (hD'L : Nonempty (D'.twistModule c ε ≅ (L.pullbackAlong ψ).L))
    (h1' : ∀ (k : Type u) [Field k] (s' : Spec (CommRingCat.of k) ⟶ T')
      (𝒲 : (pullback (pullback.snd c t') s').TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t' s') (fibreModule c t' s'
          ((L.pullbackAlong ψ).L ⊗ (sectionTwist c ε t' r ⊗ (Dγ.pullbackAlong t' (Category.comp_id t')).idealModule)))).H1) :
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
        (Lψ.L ⊗ (sectionTwist c ε (ψ1 ≫ t) (g + e) ⊗ DγT'.idealModule)))).H1 ∧
      Module.finrank k (𝒲.sectionsOf (fibreAt c (ψ1 ≫ t) s') (fibreModule c (ψ1 ≫ t) s'
        (Lψ.L ⊗ (sectionTwist c ε (ψ1 ≫ t) (g + e) ⊗ DγT'.idealModule)))).H0 = 1 :=
    fun k _ s' 𝒲 => ⟨h1' k s' 𝒲,
      hH0one (ψ1 ≫ t) Lψ hL' k s' 𝒲 (h1' k s' 𝒲)⟩
  refine ⟨?_, ?_⟩
  ·
    rintro _ ⟨y, rfl⟩
    have key := hWmax (T'.residueField y) (T'.fromSpecResidueField y ≫ ψ1) (fun 𝒲 => by
      obtain ⟨𝒱, -, ⟨e1⟩⟩ := fibre_transport_to_t' R c ε U hεU (g + e) Dγ hDγ t ψ1 L (T'.fromSpecResidueField y) 𝒲
      haveI := h1' _ (T'.fromSpecResidueField y) 𝒱
      exact e1.symm.toEquiv.subsingleton)
    refine key ⟨IsLocalRing.closedPoint (T'.residueField y), ?_⟩
    rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
  ·
    intro φ hφ
    have hφt : φ ≫ (W.ι ≫ t) = ψ1 ≫ t := by rw [← Category.assoc, hφ]
    have hDU : D.SupportedIn U := by
      intro x hx
      rw [hD] at hx
      change x ∈ ((D₀.I * (Dγ.pullbackAlong (W.ι ≫ t) (Category.comp_id _)).I).support : Set _) at hx
      rw [Scheme.IdealSheafData.support_mul, TopologicalSpace.Closeds.coe_sup] at hx
      exact hx.elim (fun h => hD₀U h) (fun h => (hDγ.pullbackAlong (W.ι ≫ t) (Category.comp_id _)) h)

    have hM' : Scheme.Modules.IsInvertible (Lψ.L ⊗ (sectionTwist c ε (ψ1 ≫ t) (g + e) ⊗ DγT'.idealModule)) :=
      isInvertible_Mγ R c ε U hεU (ψ1 ≫ t) Lψ DγT' hDγT'

    obtain ⟨N₁, hN₁, ⟨e₁⟩⟩ := exists_lineBundle_iso_of_twistModule_iso R c ε U hεU (ψ1 ≫ t) Lψ DγT' hDγT' D₀' hD₀'U D' hD' hD'L

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
    have hDL₂ : Nonempty ((D.pullbackAlong φ hφt).twistModule c ε ≅ Lψ.L) := by
      obtain ⟨i⟩ := RelEffCartierDiv.nonempty_twistModule_pullbackAlong_iso_pullback_of_supportedIn c ε U hεU
        (⟨φ, hφt⟩ : SchemeHomOver (ψ1 ≫ t) (W.ι ≫ t)) D hDU
      exact ⟨i ≪≫ (Scheme.Modules.pullback _).mapIso hDL.some ≪≫ eL⟩
    obtain ⟨N₂, hN₂, ⟨e₂⟩⟩ := exists_lineBundle_iso_of_twistModule_iso R c ε U hεU (ψ1 ≫ t) Lψ DγT' hDγT'
      (D₀.pullbackAlong φ hφt) (hD₀U.pullbackAlong φ hφt) (D.pullbackAlong φ hφt) hD₂ hDL₂

    obtain ⟨D₀'', N'', -, -, huq⟩ := hsect (ψ1 ≫ t) _ hM' hfib' (hZfibγ (ψ1 ≫ t) Lψ hL')
    have huniq : D₀'.I = (D₀.pullbackAlong φ hφt).I :=
      (huq g D₀' N₁ hN₁ hD₀'U ⟨e₁⟩).trans (huq g (D₀.pullbackAlong φ hφt) N₂ hN₂ (hD₀U.pullbackAlong φ hφt) ⟨e₂⟩).symm

    refine RelEffCartierDiv.ext ?_
    rw [hD', hD₂, huniq]

end AlgebraicGeometry.RelPicard.K5bUniv

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_relEffCartierDiv_eq_pullbackAlong_of_twistModule_iso_of_supportedIn_of_zeroScheme.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_relEffCartierDiv_eq_pullbackAlong_of_twistModule_iso_of_supportedIn_of_zeroScheme.AlgebraicGeometry.RelPicard NeronModelInfra"

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)] (hεU : Set.range ε.1 ⊆ (U : Set C))
    (g e r : ℕ) (hr : g + e = r) (Dγ : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R)))) (hDγ : Dγ.SupportedIn U)
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
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule))), σ ≠ 0 →
        ∃ Dx : RelEffCartierDiv c g (x ≫ t), Dx.I = Scheme.Modules.zeroSchemeIdeal σ ∧ Dx.SupportedIn U)
    (hH0one : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) (L : RigidifiedLineBundle c ε t), FibrewiseAlgEquivZero L →
      ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T) (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))).H1 →
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))).H0 = 1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (L : RigidifiedLineBundle c ε t) (hL : FibrewiseAlgEquivZero L) (W : T.Opens)
    (hWmax : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
      (∀ (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))).H1) → Set.range ⇑s ⊆ (W : Set T))
    (D : RelEffCartierDiv c r (W.ι ≫ t)) (D₀ : RelEffCartierDiv c g (W.ι ≫ t))
    (hD : D.I = D₀.I * (Dγ.pullbackAlong (W.ι ≫ t) (Category.comp_id _)).I) (hD₀U : D₀.SupportedIn U)
    (hDL : Nonempty (D.twistModule c ε ≅ (L.pullbackAlong (⟨W.ι, rfl⟩ : SchemeHomOver (W.ι ≫ t) t)).L))
    {T' : Scheme.{u}} (t' : T' ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t'] (ψ : SchemeHomOver t' t)
    (D' : RelEffCartierDiv c r t') (D₀' : RelEffCartierDiv c g t')
    (hD' : D'.I = D₀'.I * (Dγ.pullbackAlong t' (Category.comp_id _)).I) (hD₀'U : D₀'.SupportedIn U)
    (hD'L : Nonempty (D'.twistModule c ε ≅ (L.pullbackAlong ψ).L))
    (h1' : ∀ (k : Type u) [Field k] (s' : Spec (CommRingCat.of k) ⟶ T')
      (𝒲 : (pullback (pullback.snd c t') s').TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t' s') (fibreModule c t' s'
          ((L.pullbackAlong ψ).L ⊗ (sectionTwist c ε t' r ⊗ (Dγ.pullbackAlong t' (Category.comp_id t')).idealModule)))).H1) :
    Set.range ⇑ψ.1 ⊆ (W : Set T) ∧
      ∀ (φ : T' ⟶ W) (hφ : φ ≫ W.ι = ψ.1),
        D' = D.pullbackAlong φ (by rw [← Category.assoc, hφ]; exact ψ.2) :=
  AlgebraicGeometry.RelPicard.K5bUniv.UNIV' R c ε U hεU g e r hr Dγ hDγ hsect hZfibγ hH0one t L hL W hWmax D D₀ hD hD₀U hDL t' ψ D' D₀' hD' hD₀'U hD'L h1'

end S_AlgebraicGeometry_RelPicard_relEffCartierDiv_eq_pullbackAlong_of_twistModule_iso_of_supportedIn_of_zeroScheme
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_relEffCartierDiv_eq_pullbackAlong_of_twistModule_iso_of_supportedIn_of_zeroScheme (solution)
