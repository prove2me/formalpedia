-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_unit_of_closedCover_of_forall_pullbackSection_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/110670f3-1626-5788-8390-58e272d65207

import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicCurve_RelCartier
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullbackSection_eq_zero_iff_mem_support
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_comap_zeroSchemeIdeal
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_iso_invModule_zeroSchemeIdeal
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_unique_section_of_pullbackSection_closedCover
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_eq_of_forall_pullbackSection_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_unit_of_closedCover_of_forall_pullbackSection_eq
p2m_attr_erase "instance" "SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_unit_of_closedCover_of_forall_pullbackSection_eq.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.IdealSheafData.support_comap Scheme.Modules.Hom.zero_app Scheme.Modules.pullback Scheme.Modules.Hom LocallyOfFiniteType Spec Scheme Scheme.Modules.Hom.id_app Scheme.IdealSheafData.support_top IsClosedImmersion IsReduced Scheme.Modules.pullbackCongr Scheme.fromSpecResidueField_apply Scheme.IdealSheafData.support_eq_bot_iff Scheme.Modules Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.ΓSpecIso Scheme.Modules.pullbackSection Scheme.IdealSheafData.invModule Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso Scheme.Modules.isInvertible_unit Scheme.IdealSheafData.isInvertible_top Scheme.Modules.exists_unique_section_of_pullbackSection_closedCover Scheme.Modules.IsInvertible.eq_of_forall_pullbackSection_eq"
namespace GluingKernel
p2m_open "AlgebraicGeometry"

p2m_open "AlgebraicGeometry.Scheme.Modules"

lemma id_tensorUnit_ne_zero (S : Scheme.{u}) [Nontrivial Γ(S, ⊤)] :
    (𝟙 (𝟙_ S.Modules)) ≠ 0 := by
  intro h
  have h1 := congrArg (fun φ : (𝟙_ S.Modules) ⟶ 𝟙_ S.Modules =>
    ofUnitSection ⊤ (φ.app ⊤ (toUnitSection ⊤ 1))) h
  simp only [Scheme.Modules.Hom.id_app, Scheme.Modules.Hom.zero_app] at h1
  change ofUnitSection ⊤ (toUnitSection ⊤ (1 : Γ(S, ⊤))) =
    ofUnitSection ⊤ (0 : Γ(𝟙_ S.Modules, ⊤)) at h1
  rw [ofUnitSection_toUnitSection] at h1
  haveI : Subsingleton Γ(S, ⊤) := subsingleton_of_zero_eq_one (h1 : (1 : Γ(S, ⊤)) = 0).symm
  exact false_of_nontrivial_of_subsingleton Γ(S, ⊤)

scoped instance nontrivial_Γ_Spec (K : Type u) [Field K] : Nontrivial Γ(Spec (CommRingCat.of K), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toEquiv.nontrivial

theorem zeroSchemeIdeal_eq_top_of_isIso {Y : Scheme.{u}} {N : Y.Modules} (hN : Scheme.Modules.IsInvertible N)
    (s : 𝟙_ Y.Modules ⟶ N) [IsIso s] : zeroSchemeIdeal s = ⊤ := by
  rw [← Scheme.IdealSheafData.support_eq_bot_iff]
  refine le_antisymm (fun y hy => ?_) bot_le
  exfalso
  have hmem : (Y.fromSpecResidueField y).base (IsLocalRing.closedPoint (Y.residueField y)) ∈
      (zeroSchemeIdeal s).support := by
    rw [Scheme.fromSpecResidueField_apply]; exact hy
  have h0 := (hN.pullbackSection_eq_zero_iff_mem_support (k := Y.residueField y) s
    (Y.fromSpecResidueField y)).mpr hmem

  have hid : pullbackSection (Y.fromSpecResidueField y) s ≫
      (inv ((Scheme.Modules.pullback (Y.fromSpecResidueField y)).map s) ≫
        (pullbackUnitIso (Y.fromSpecResidueField y)).hom) = 𝟙 _ := by
    simp [pullbackSection_def]
  haveI : Nontrivial Γ(Spec (Y.residueField y), ⊤) := nontrivial_Γ_Spec (Y.residueField y)
  apply id_tensorUnit_ne_zero (Spec (Y.residueField y))
  rw [← hid, h0, zero_comp]
  rfl

theorem nonempty_iso_unit_of_isIso_pullbackSection {X Y₁ Y₂ : Scheme.{u}} (i₁ : Y₁ ⟶ X) (i₂ : Y₂ ⟶ X)
    (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    {L : X.Modules} (hL : Scheme.Modules.IsInvertible L) (σ : 𝟙_ X.Modules ⟶ L)
    [IsIso (pullbackSection i₁ σ)] [IsIso (pullbackSection i₂ σ)] :
    Nonempty (L ≅ 𝟙_ X.Modules) := by
  have hZ : zeroSchemeIdeal σ = ⊤ := by
    rw [← Scheme.IdealSheafData.support_eq_bot_iff]
    refine le_antisymm (fun x hx => ?_) bot_le
    exfalso
    rcases (Set.eq_univ_iff_forall.mp hcover x) with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · have hy : y ∈ ((zeroSchemeIdeal σ).comap i₁).support := by
        rw [Scheme.IdealSheafData.support_comap]; exact hx
      rw [hL.comap_zeroSchemeIdeal i₁ σ, zeroSchemeIdeal_eq_top_of_isIso (hL.pullback i₁),
        Scheme.IdealSheafData.support_top] at hy
      exact hy
    · have hy : y ∈ ((zeroSchemeIdeal σ).comap i₂).support := by
        rw [Scheme.IdealSheafData.support_comap]; exact hx
      rw [hL.comap_zeroSchemeIdeal i₂ σ, zeroSchemeIdeal_eq_top_of_isIso (hL.pullback i₂),
        Scheme.IdealSheafData.support_top] at hy
      exact hy

  have h1 : Scheme.Modules.IsInvertible (𝟙_ X.Modules) := Scheme.Modules.isInvertible_unit X
  have hZ1 : zeroSchemeIdeal (𝟙 (𝟙_ X.Modules)) = ⊤ := zeroSchemeIdeal_eq_top_of_isIso h1 (𝟙 (𝟙_ X.Modules))
  obtain ⟨e, -⟩ := hL.exists_iso_invModule_zeroSchemeIdeal σ (hZ ▸ Scheme.IdealSheafData.isInvertible_top)
  obtain ⟨e', -⟩ := h1.exists_iso_invModule_zeroSchemeIdeal (𝟙 (𝟙_ X.Modules))
    (hZ1 ▸ Scheme.IdealSheafData.isInvertible_top)
  exact ⟨e ≪≫ eqToIso (congrArg Scheme.IdealSheafData.invModule (hZ.trans hZ1.symm)) ≪≫ e'.symm⟩

end AlgebraicGeometry.GluingKernel
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_unit_of_closedCover_of_forall_pullbackSection_eq.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_unit_of_closedCover_of_forall_pullbackSection_eq.AlgebraicGeometry.GluingKernel"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_unit_of_closedCover_of_forall_pullbackSection_eq.AlgebraicGeometry"

open AlgebraicGeometry.GluingKernel _root_.AlgebraicGeometry.Scheme.Modules in
theorem solution
    {k : Type u} [Field k] [IsAlgClosed k] {X Y₁ Y₂ : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    [IsReduced X] [LocallyOfFiniteType x]
    (i₁ : Y₁ ⟶ X) (i₂ : Y₂ ⟶ X) [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ) (htrans : IsReduced (Limits.pullback i₁ i₂))
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (τ₁ : (Scheme.Modules.pullback i₁).obj L ≅ (Scheme.Modules.pullback i₁).obj (𝟙_ X.Modules))
    (τ₂ : (Scheme.Modules.pullback i₂).obj L ≅ (Scheme.Modules.pullback i₂).obj (𝟙_ X.Modules))
    (hpts : ∀ p : Spec (CommRingCat.of k) ⟶ Limits.pullback i₁ i₂, p ≫ (Limits.pullback.fst i₁ i₂ ≫ i₁ ≫ x) = 𝟙 _ →
      Scheme.Modules.pullbackSection p
          (Scheme.Modules.pullbackSection (Limits.pullback.fst i₁ i₂) ((Scheme.Modules.pullbackUnitIso i₁).inv ≫ τ₁.inv) ≫
            ((Scheme.Modules.pullbackComp (Limits.pullback.fst i₁ i₂) i₁).app L).hom ≫
              ((Scheme.Modules.pullbackCongr (Limits.pullback.condition (f := i₁) (g := i₂))).app L).hom) =
        Scheme.Modules.pullbackSection p
          (Scheme.Modules.pullbackSection (Limits.pullback.snd i₁ i₂) ((Scheme.Modules.pullbackUnitIso i₂).inv ≫ τ₂.inv) ≫
            ((Scheme.Modules.pullbackComp (Limits.pullback.snd i₁ i₂) i₂).app L).hom)) :
    Nonempty (L ≅ SheafOfModules.unit X.ringCatSheaf) := by
  haveI : IsReduced (pullback i₁ i₂) := htrans

  have hagree := Scheme.Modules.IsInvertible.eq_of_forall_pullbackSection_eq (pullback.fst i₁ i₂ ≫ i₁ ≫ x)
    (hL.pullback (pullback.snd i₁ i₂ ≫ i₂)) _ _ hpts

  obtain ⟨σ, hσ₁, hσ₂, -⟩ := Scheme.Modules.exists_unique_section_of_pullbackSection_closedCover i₁ i₂ hcover L hL
    ((Scheme.Modules.pullbackUnitIso i₁).inv ≫ τ₁.inv) ((Scheme.Modules.pullbackUnitIso i₂).inv ≫ τ₂.inv) hagree
  haveI : IsIso (pullbackSection i₁ σ) := by
    rw [hσ₁]; exact (inferInstance : IsIso (τ₁ ≪≫ Scheme.Modules.pullbackUnitIso i₁).inv)
  haveI : IsIso (pullbackSection i₂ σ) := by
    rw [hσ₂]; exact (inferInstance : IsIso (τ₂ ≪≫ Scheme.Modules.pullbackUnitIso i₂).inv)
  exact nonempty_iso_unit_of_isIso_pullbackSection i₁ i₂ hcover hL σ

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_unit_of_closedCover_of_forall_pullbackSection_eq
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_unit_of_closedCover_of_forall_pullbackSection_eq (solution)
