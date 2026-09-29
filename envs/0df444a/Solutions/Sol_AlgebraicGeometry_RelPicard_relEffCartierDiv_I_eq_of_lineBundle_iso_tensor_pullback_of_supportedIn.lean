-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.relEffCartierDiv_I_eq_of_lineBundle_iso_tensor_pullback_of_supportedIn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/10f32d6e-f789-56d3-bb2f-bceaef5d371d

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal

import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import Definitions.Def_AlgebraicCurve_RelCartier
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_one_iff_isInvertible
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_zeroSchemeIdeal_comp_eq_of_isIso
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_zeroSchemeIdeal_invModuleSection
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I_of_supportedIn
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_eq_of_forall_comap_openCover_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_comap_zeroSchemeIdeal
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_tensor_pullback_iso_of_trivial_on_open
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_zeroSchemeIdeal_eq_of_app_eq_smul
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_ModulesPushforwardRestrict
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_relEffCartierDiv_I_eq_of_lineBundle_iso_tensor_pullback_of_supportedIn
p2m_attr_erase "instance" "SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver"
p2m_attr_erase "simp" "PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_relEffCartierDiv_I_eq_of_lineBundle_iso_tensor_pullback_of_supportedIn.AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra"

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Scheme.Modules.Hom.app_smul Scheme.Modules.Hom.mapPresheaf Scheme.IdealSheafData.support_comap SmoothOfRelativeDimension Scheme.Modules.pushforward IsProper morphismRestrict_base_coe Scheme.Modules.pullback Scheme.Hom Scheme.Modules.Hom.comp_app Scheme.Hom.germ_stalkMap_apply Scheme.Opens.ι_appIso Scheme.Modules.Hom LocallyOfFiniteType Spec Scheme.Modules.mapPresheaf_app Scheme Scheme.Modules.Hom.id_app Scheme.Modules.restrictFunctorIsoPullback Scheme.Opens.topIso_hom Scheme.basicOpen_zero Scheme.zeroLocus_span IsSeparated Scheme.mem_zeroLocus_iff Scheme.Modules.pullbackCongr RingedSpace.isUnit_of_isUnit_germ Scheme.Cover.mkOfCovers Scheme.fromSpecResidueField_apply IsAffineOpen Scheme.Modules Scheme.Opens Scheme.basicOpen_one Scheme.IdealSheafData.coe_support_inter Scheme.Pullback.exists_preimage_pullback Scheme.IdealSheafData.mem_support_iff_of_mem Scheme.Modules.map_smul Scheme.Hom.comp_apply RingedSpace geometrically Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.Cover Scheme.Modules.IsInvertible RelEffCartierDiv mapOnProdOver mapOnProdOver_fst mapOnProdOver_snd Scheme.Modules.toUnitSection Scheme.Modules.ofUnitSection Scheme.Modules.ofUnitSection_toUnitSection Scheme.Modules.ofUnitSection_injective Scheme.Modules.ofUnitSection_map Scheme.Modules.ofUnitSection_smul Scheme.Modules.restrictSection Scheme.Modules.coeff Scheme.Modules.zeroSchemeIdeal Scheme.Modules.pullbackSection Scheme.Modules.IsLocallyFreeOfRank Scheme.IdealSheafData.IsInvertible Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso Scheme.IdealSheafData.eq_of_forall_comap_openCover_eq Scheme.Modules.nonempty_pullback_tensor_pullback_iso_of_trivial_on_open Scheme.Modules.IsInvertible.zeroSchemeIdeal_eq_of_app_eq_smul Scheme.Modules.pushforwardRestrictIso Scheme.Modules.IsInvertible.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq" namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "mem_basicOpen fromSpecResidueField Modules.Hom.app_smul Modules.Hom.mapPresheaf IdealSheafData.support_comap Modules.pushforward Modules.pullback Hom.id_app Hom Γ Modules.Hom.comp_app Hom.germ_stalkMap_apply Opens.ι_appIso topIso_hom Modules.Hom topIso Modules.mapPresheaf_app Modules.Hom.id_app Modules.restrictFunctorIsoPullback Opens.topIso_hom OpenCover basicOpen_zero zeroLocus_span affineBasicOpen mem_zeroLocus_iff Hom.comp_app basicOpen Modules.pullbackCongr Cover.mkOfCovers fromSpecResidueField_apply Modules Opens homOfLE_ι basicOpen_one IdealSheafData.coe_support_inter Pullback.exists_preimage_pullback IdealSheafData.mem_support_iff_of_mem Modules.map_smul basicOpen_le restrict Hom.comp_apply PresheafOfModules IdealSheafData Modules.pullbackComp Cover Modules.IsInvertible TwoAffineOpenCover Modules.toUnitSection Modules.ofUnitSection Modules.ofUnitSection_toUnitSection Modules.ofUnitSection_injective Modules.ofUnitSection_map Modules.ofUnitSection_smul Modules.restrictSection Modules.coeff Modules.zeroSchemeIdeal Modules.pullbackSection Modules.IsLocallyFreeOfRank IdealSheafData.IsInvertible Modules.isLocallyFreeOfRank_one_iff_isInvertible Modules.zeroSchemeIdeal_comp_eq_of_isIso IdealSheafData.eq_of_forall_comap_openCover_eq Modules.nonempty_pullback_tensor_pullback_iso_of_trivial_on_open Modules.IsInvertible.zeroSchemeIdeal_eq_of_app_eq_smul Modules.pushforwardRestrictIso Modules.IsInvertible.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq" namespace IdealSheafData p2m_export "AlgebraicGeometry.Scheme.IdealSheafData" "support_comap map map_id ideal map_comp comap coe_support_inter support mem_support_iff_of_mem module invModuleSection IsInvertible eq_of_forall_comap_openCover_eq" namespace IsInvertible p2m_export "AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible" "mul zeroSchemeIdeal_invModuleSection" end AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible
namespace AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.IdealSheafData AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible" in

private theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.exists_notMem_support
    {X : Scheme.{u}} {I : X.IdealSheafData} (hI : I.IsInvertible) (x : X) :
    ∃ y : X, y ∉ I.support := by
  obtain ⟨U, f, hxf, g, hg, hIg⟩ := hI x
  have hB : IsAffineOpen (X.affineBasicOpen f : X.Opens) := (X.affineBasicOpen f).2

  have hnil : ¬ IsNilpotent g := by
    rintro ⟨n, hn⟩
    rcases subsingleton_or_nontrivial Γ(X, X.affineBasicOpen f) with hsub | hnt
    · have h1 : X.basicOpen (1 : Γ(X, X.affineBasicOpen f)) = ⊥ := by
        rw [Subsingleton.elim (1 : Γ(X, X.affineBasicOpen f)) 0, Scheme.basicOpen_zero]
      rw [Scheme.basicOpen_one] at h1
      have hx' : x ∈ ((X.affineBasicOpen f : X.Opens) : Set X) := hxf
      rw [h1] at hx'
      exact hx'
    · exact nonZeroDivisors.ne_zero (pow_mem hg n) hn

  obtain ⟨J, hJ, hgJ⟩ : ∃ J : Ideal Γ(X, X.affineBasicOpen f), J.IsPrime ∧ g ∉ J := by
    by_contra h
    push_neg at h
    exact hnil (nilpotent_iff_mem_prime.mpr h)
  let p : PrimeSpectrum Γ(X, X.affineBasicOpen f) := ⟨J, hJ⟩
  refine ⟨hB.fromSpec.base p, fun hy => ?_⟩
  have hyg : hB.fromSpec.base p ∈ X.basicOpen g := by
    show p ∈ hB.fromSpec ⁻¹ᵁ X.basicOpen g
    rw [hB.fromSpec_preimage_basicOpen]
    exact hgJ
  have hyB : hB.fromSpec.base p ∈ ((X.affineBasicOpen f : X.Opens) : Set X) := X.basicOpen_le g hyg
  have hz : hB.fromSpec.base p ∈ (I.support : Set X) ∩ (X.affineBasicOpen f : X.Opens) := ⟨hy, hyB⟩
  rw [Scheme.IdealSheafData.coe_support_inter, hIg] at hz
  exact (X.mem_zeroLocus_iff _ _).mp hz.1 g (Ideal.subset_span rfl) hyg

end AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible
p2m_export "" "AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.exists_notMem_support"
namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Scheme.Modules.Hom.app_smul Scheme.Modules.Hom.mapPresheaf Scheme.IdealSheafData.support_comap SmoothOfRelativeDimension Scheme.Modules.pushforward IsProper morphismRestrict_base_coe Scheme.Modules.pullback Scheme.Hom Scheme.Modules.Hom.comp_app Scheme.Hom.germ_stalkMap_apply Scheme.Opens.ι_appIso Scheme.Modules.Hom LocallyOfFiniteType Spec Scheme.Modules.mapPresheaf_app Scheme Scheme.Modules.Hom.id_app Scheme.Modules.restrictFunctorIsoPullback Scheme.Opens.topIso_hom Scheme.basicOpen_zero Scheme.zeroLocus_span IsSeparated Scheme.mem_zeroLocus_iff Scheme.Modules.pullbackCongr RingedSpace.isUnit_of_isUnit_germ Scheme.Cover.mkOfCovers Scheme.fromSpecResidueField_apply IsAffineOpen Scheme.Modules Scheme.Opens Scheme.basicOpen_one Scheme.IdealSheafData.coe_support_inter Scheme.Pullback.exists_preimage_pullback Scheme.IdealSheafData.mem_support_iff_of_mem Scheme.Modules.map_smul Scheme.Hom.comp_apply RingedSpace geometrically Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.Cover Scheme.Modules.IsInvertible RelEffCartierDiv mapOnProdOver mapOnProdOver_fst mapOnProdOver_snd Scheme.Modules.toUnitSection Scheme.Modules.ofUnitSection Scheme.Modules.ofUnitSection_toUnitSection Scheme.Modules.ofUnitSection_injective Scheme.Modules.ofUnitSection_map Scheme.Modules.ofUnitSection_smul Scheme.Modules.restrictSection Scheme.Modules.coeff Scheme.Modules.zeroSchemeIdeal Scheme.Modules.pullbackSection Scheme.Modules.IsLocallyFreeOfRank Scheme.IdealSheafData.IsInvertible Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso Scheme.IdealSheafData.eq_of_forall_comap_openCover_eq Scheme.Modules.nonempty_pullback_tensor_pullback_iso_of_trivial_on_open Scheme.Modules.IsInvertible.zeroSchemeIdeal_eq_of_app_eq_smul Scheme.Modules.pushforwardRestrictIso Scheme.Modules.IsInvertible.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq" namespace RelEffCartierDiv p2m_export "AlgebraicGeometry.RelEffCartierDiv" "lineBundle ext pullbackAlong I SupportedIn isInvertible_I_of_supportedIn" end AlgebraicGeometry.RelEffCartierDiv
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.RelEffCartierDiv" in

theorem AlgebraicGeometry.RelEffCartierDiv.exists_snd_apply_eq_and_notMem_support_of_supportedIn
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) {d : ℕ} (D : RelEffCartierDiv c d t) (hDU : D.SupportedIn U)
    (x : T) (hx : ∃ y : ↥(pullback c t), (pullback.snd c t).base y = x) :
    ∃ y : ↥(pullback c t), (pullback.snd c t).base y = x ∧ y ∉ D.I.support := by
  obtain ⟨y₀, hy₀⟩ := hx
  let s := T.fromSpecResidueField x
  let F : pullback c (s ≫ t) ⟶ pullback c t := mapOnProdOver c s (rfl : s ≫ t = s ≫ t)

  obtain ⟨w, hw1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd c t) (g := s) y₀
    (IsLocalRing.closedPoint _) (by rw [hy₀]; exact (Scheme.fromSpecResidueField_apply x _).symm)
  have hcomp : (pullbackLeftPullbackSndIso c t s).hom ≫ F = pullback.fst (pullback.snd c t) s := by
    apply pullback.hom_ext
    · rw [Category.assoc, mapOnProdOver_fst c s (rfl : s ≫ t = s ≫ t), pullbackLeftPullbackSndIso_hom_fst]
    · rw [Category.assoc, mapOnProdOver_snd c s (rfl : s ≫ t = s ≫ t), pullbackLeftPullbackSndIso_hom_snd_assoc, pullback.condition]
  let z : ↥(pullback c (s ≫ t)) := (pullbackLeftPullbackSndIso c t s).hom.base w

  have hinv : (D.pullbackAlong s rfl).I.IsInvertible :=
    (D.pullbackAlong s rfl).isInvertible_I_of_supportedIn U (hDU.pullbackAlong s rfl)
  obtain ⟨y, hy⟩ := hinv.exists_notMem_support z
  refine ⟨F.base y, ?_, fun hsupp => hy ?_⟩
  · rw [← Scheme.Hom.comp_apply, mapOnProdOver_snd c s (rfl : s ≫ t = s ≫ t), Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply x _
  · change y ∈ (D.I.comap F).support
    rw [Scheme.IdealSheafData.support_comap]
    exact hsupp

namespace K5aUnitWs13

open Opposite TopologicalSpace

variable {X : Scheme.{u}} {M : X.Modules}

theorem map_app_unit (φ : 𝟙_ X.Modules ⟶ M) {U V : X.Opens} (i : U ⟶ V)
    (m : Γ(𝟙_ X.Modules, V)) :
    M.presheaf.map i.op (φ.app V m) = φ.app U ((𝟙_ X.Modules).presheaf.map i.op m) := by
  have h := (Scheme.Modules.Hom.mapPresheaf φ).naturality i.op
  have h2 := ConcreteCategory.congr_hom h m
  simp only [Scheme.Modules.mapPresheaf_app, ConcreteCategory.comp_apply] at h2
  exact h2.symm

theorem map_toUnitSection_one {U V : X.Opens} (i : U ⟶ V) :
    (𝟙_ X.Modules).presheaf.map i.op (Scheme.Modules.toUnitSection V 1) =
      Scheme.Modules.toUnitSection U 1 := by
  apply Scheme.Modules.ofUnitSection_injective
  rw [Scheme.Modules.ofUnitSection_map, Scheme.Modules.ofUnitSection_toUnitSection,
    Scheme.Modules.ofUnitSection_toUnitSection, map_one]

theorem app_one_eq_map (φ : 𝟙_ X.Modules ⟶ M) (U : X.Opens) :
    φ.app U (Scheme.Modules.toUnitSection U 1) =
      M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (φ.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)) := by
  rw [map_app_unit, map_toUnitSection_one]

noncomputable def homOfGlobal (M : X.Modules) (m : Γ(M, ⊤)) : 𝟙_ X.Modules ⟶ M :=
  (SheafOfModules.unitHomEquiv M).symm
    (PresheafOfModules.sectionsMk (fun U => M.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op m)
      (by
        intro U V f
        change (M.presheaf.map (homOfLE _).op ≫ M.presheaf.map f) m = _
        rw [← Functor.map_comp]
        rfl))

theorem homOfGlobal_app_top (M : X.Modules) (m : Γ(M, ⊤)) :
    (homOfGlobal M m).app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) = m := by
  have hS : ∀ ⦃U V : (X.Opens)ᵒᵖ⦄ (f : U ⟶ V),
      M.presheaf.map f (M.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op m) =
        M.presheaf.map (homOfLE (le_top : V.unop ≤ ⊤)).op m := by
    intro U V f
    change (M.presheaf.map (homOfLE _).op ≫ M.presheaf.map f) m = _
    rw [← Functor.map_comp]
    rfl
  have h := congrArg (fun s : M.val.sections => s.val (op ⊤))
    ((SheafOfModules.unitHomEquiv M).apply_symm_apply
      (PresheafOfModules.sectionsMk (fun U => M.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op m) hS))
  simp only [PresheafOfModules.sectionsMk_coe] at h
  have hm : M.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op m = m := by
    rw [show (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)) = 𝟙 _ from rfl, op_id, CategoryTheory.Functor.map_id]; rfl
  rw [hm] at h
  have h2 : ∀ σ : 𝟙_ X.Modules ⟶ M,
      ((SheafOfModules.unitHomEquiv M) σ).val (op ⊤) = σ.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) := by
    intro σ
    simp only [SheafOfModules.unitHomEquiv, Equiv.trans_apply]
    erw [PresheafOfModules.unitHomEquiv_apply_coe]
    rfl
  rw [← h2]
  exact h

theorem coeff_eq_mul_coeff (s s' : 𝟙_ X.Modules ⟶ M) (u : Γ(X, ⊤))
    (h : s.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) = u • s'.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1))
    (U : X.Opens) (τ : M.restrict U.ι ≅ 𝟙_ ((U : Scheme.{u})).Modules) :
    Scheme.Modules.coeff s U τ.hom =
      X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op u * Scheme.Modules.coeff s' U τ.hom := by
  set W : X.Opens := U.ι ''ᵁ ⊤ with hW
  have hres : s.app W (Scheme.Modules.toUnitSection W 1) =
      X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op u • s'.app W (Scheme.Modules.toUnitSection W 1) := by
    rw [app_one_eq_map s W, app_one_eq_map s' W, h, Scheme.Modules.map_smul]
  set r : Γ((U : Scheme.{u}), ⊤) := X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op u with hr
  have hres' : Scheme.Modules.restrictSection s U = r • Scheme.Modules.restrictSection s' U := by
    change s.app W (Scheme.Modules.toUnitSection W 1) =
      (U.ι.appIso ⊤).inv r • s'.app W (Scheme.Modules.toUnitSection W 1)
    rw [Scheme.Opens.ι_appIso, Iso.refl_inv]
    exact hres
  have key : Scheme.Modules.coeff s U τ.hom = U.topIso.hom r * Scheme.Modules.coeff s' U τ.hom := by
    show U.topIso.hom (Scheme.Modules.ofUnitSection ⊤ (τ.hom.app ⊤ (Scheme.Modules.restrictSection s U))) = _
    rw [hres', Scheme.Modules.Hom.app_smul, Scheme.Modules.ofUnitSection_smul, map_mul]
    rfl
  rw [key, hr, Scheme.Opens.topIso_hom]
  congr 1
  change (X.presheaf.map _ ≫ X.presheaf.map _) u = _
  rw [← Functor.map_comp]
  rfl

theorem isUnit_coord_of_forall_fibre {T : Scheme.{u}} (q : X ⟶ T) (hM : Scheme.Modules.IsInvertible M)
    (τ : (Scheme.Modules.pushforward q).obj M ≅ 𝟙_ T.Modules) (s : 𝟙_ X.Modules ⟶ M)
    (hs : ∀ x : T, ∃ y : X, q.base y = x ∧ y ∉ (Scheme.Modules.zeroSchemeIdeal s).support) :
    IsUnit (Scheme.Modules.ofUnitSection ⊤
      (τ.hom.app ⊤ (show Γ((Scheme.Modules.pushforward q).obj M, ⊤) from
        s.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)))) := by
  classical
  set m : Γ((Scheme.Modules.pushforward q).obj M, ⊤) := s.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) with hm
  set a : Γ(T, ⊤) := Scheme.Modules.ofUnitSection ⊤ (τ.hom.app ⊤ m) with ha
  set e : Γ((Scheme.Modules.pushforward q).obj M, ⊤) := τ.inv.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) with he

  have h1 : τ.hom.app ⊤ m = a • Scheme.Modules.toUnitSection ⊤ 1 := by
    apply Scheme.Modules.ofUnitSection_injective
    rw [Scheme.Modules.ofUnitSection_smul, Scheme.Modules.ofUnitSection_toUnitSection, mul_one]
  have h2 : m = τ.inv.app ⊤ (τ.hom.app ⊤ m) := by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id,
      Scheme.Modules.Hom.id_app]
    rfl
  have hme : m = a • e := by
    calc m = τ.inv.app ⊤ (τ.hom.app ⊤ m) := h2
      _ = τ.inv.app ⊤ (a • Scheme.Modules.toUnitSection ⊤ 1) := by rw [h1]
      _ = a • e := by rw [Scheme.Modules.Hom.app_smul]

  have hme' : s.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) = q.appTop a • (show Γ(M, ⊤) from e) := hme

  apply RingedSpace.isUnit_of_isUnit_germ
  intro x _
  obtain ⟨y, hyx, hy⟩ := hs x
  obtain ⟨U, hyU, -, ⟨τU⟩⟩ := hM.exists_restrict_iso (V := ⊤) (x := y) trivial

  have hZU := ((Scheme.Modules.IsInvertible.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq hM s).2 U τU).1
  have hyb : y ∈ X.basicOpen (Scheme.Modules.coeff s U.1 τU.hom) := by
    by_contra hyb
    apply hy
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem hyU, hZU, Scheme.zeroLocus_span, Scheme.mem_zeroLocus_iff]
    intro f hf
    rw [Set.mem_singleton_iff] at hf
    rw [hf]; exact hyb
  have hunit := (X.mem_basicOpen _ y hyU).mp hyb

  have hcmp := coeff_eq_mul_coeff s (homOfGlobal M (show Γ(M, ⊤) from e)) (q.appTop a)
    (by rw [homOfGlobal_app_top]; exact hme') U.1 τU
  rw [hcmp, map_mul] at hunit
  have hu1 := isUnit_of_mul_isUnit_left hunit

  rw [TopCat.Presheaf.germ_res_apply] at hu1
  have hq : X.presheaf.germ ⊤ y trivial (q.appTop a) =
      q.stalkMap y (T.presheaf.germ ⊤ (q.base y) trivial a) :=
    (Scheme.Hom.germ_stalkMap_apply q ⊤ y trivial a).symm
  rw [hq] at hu1
  rw [← hyx]
  exact (isUnit_map_iff (q.stalkMap y).hom _).mp hu1

end K5aUnitWs13

set_option maxHeartbeats 6400000 in
theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (hpush : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
      (F : (pullback c t).Modules), Scheme.Modules.IsInvertible F → ∀ (n : ℕ),
      (∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T) (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F)).H1 ∧
          Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F)).H0 = n) →
      Scheme.Modules.IsLocallyFreeOfRank n ((Scheme.Modules.pushforward (pullback.snd c t)).obj F))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (M : (pullback c t).Modules) (hM : Scheme.Modules.IsInvertible M)
    (hfib : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H0 = 1)
    (hne : ∀ x : T, ∃ y : ↥(pullback c t), (pullback.snd c t).base y = x)
    {d₁ d₂ : ℕ} (D₁ : RelEffCartierDiv c d₁ t) (D₂ : RelEffCartierDiv c d₂ t)
    (hD₁U : D₁.SupportedIn U) (hD₂U : D₂.SupportedIn U)
    (N₁ N₂ : T.Modules) (hN₁ : Scheme.Modules.IsInvertible N₁) (hN₂ : Scheme.Modules.IsInvertible N₂)
    (e₁ : D₁.lineBundle ≅ M ⊗ (Scheme.Modules.pullback (pullback.snd c t)).obj N₁)
    (e₂ : D₂.lineBundle ≅ M ⊗ (Scheme.Modules.pullback (pullback.snd c t)).obj N₂) :
    D₁.I = D₂.I := by
  classical
  haveI : IsSeparated c := inferInstance
  set q := pullback.snd c t with hq

  set s₁ : 𝟙_ (pullback c t).Modules ⟶ M ⊗ (Scheme.Modules.pullback q).obj N₁ := D₁.I.invModuleSection ≫ e₁.hom with hs₁
  set s₂ : 𝟙_ (pullback c t).Modules ⟶ M ⊗ (Scheme.Modules.pullback q).obj N₂ := D₂.I.invModuleSection ≫ e₂.hom with hs₂
  have hZ₁ : Scheme.Modules.zeroSchemeIdeal s₁ = D₁.I := by
    rw [hs₁, Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso,
      (D₁.isInvertible_I_of_supportedIn U hD₁U).zeroSchemeIdeal_invModuleSection]
  have hZ₂ : Scheme.Modules.zeroSchemeIdeal s₂ = D₂.I := by
    rw [hs₂, Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso,
      (D₂.isInvertible_I_of_supportedIn U hD₂U).zeroSchemeIdeal_invModuleSection]

  have key : ∀ z : ↥(pullback c t), ∃ V : T.Opens, q.base z ∈ V ∧
      (Scheme.Modules.zeroSchemeIdeal s₁).comap (q ⁻¹ᵁ V).ι =
        (Scheme.Modules.zeroSchemeIdeal s₂).comap (q ⁻¹ᵁ V).ι := by
    intro z
    set x : T := q.base z with hxdef

    have hP : Scheme.Modules.IsInvertible ((Scheme.Modules.pushforward q).obj M) :=
      (Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible _).mp
        (hpush t M hM 1 hfib)
    obtain ⟨U₁, hxU₁, -, ⟨τ₁⟩⟩ := hN₁.exists_restrict_iso (V := ⊤) (x := x) trivial
    obtain ⟨U₂, hxU₂, h₂₁, ⟨τ₂⟩⟩ := hN₂.exists_restrict_iso (V := U₁.1) (x := x) hxU₁
    obtain ⟨U₃, hxU₃, h₃₂, ⟨τP⟩⟩ := hP.exists_restrict_iso (V := U₂.1) (x := x) hxU₂
    set V : T.Opens := U₃.1 with hVdef

    have trivN : ∀ {N : T.Modules} {U : T.Opens} (hle : V ≤ U) (τ : N.restrict U.ι ≅ 𝟙_ ((U : Scheme.{u})).Modules),
        Nonempty ((Scheme.Modules.pullback V.ι).obj N ≅ 𝟙_ ((V : Scheme.{u})).Modules) := by
      intro N U hle τ
      refine ⟨((Scheme.Modules.pullbackCongr (T.homOfLE_ι hle).symm).app N) ≪≫
        ((Scheme.Modules.pullbackComp (T.homOfLE hle) U.ι).app N).symm ≪≫
        (Scheme.Modules.pullback (T.homOfLE hle)).mapIso
          (((Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app N) ≪≫ τ) ≪≫
        (Functor.Monoidal.εIso (Scheme.Modules.pullback (T.homOfLE hle))).symm⟩
    obtain ⟨eN₁⟩ := trivN (h₃₂.trans h₂₁) τ₁
    obtain ⟨eN₂⟩ := trivN h₃₂ τ₂

    set W : (pullback c t).Opens := q ⁻¹ᵁ V with hWdef
    obtain ⟨φ₁⟩ := Scheme.Modules.nonempty_pullback_tensor_pullback_iso_of_trivial_on_open q V M N₁ eN₁
    obtain ⟨φ₂⟩ := Scheme.Modules.nonempty_pullback_tensor_pullback_iso_of_trivial_on_open q V M N₂ eN₂
    refine ⟨V, hxU₃, ?_⟩
    have hMN₁ : Scheme.Modules.IsInvertible (M ⊗ (Scheme.Modules.pullback q).obj N₁) := hM.tensor (hN₁.pullback q)
    have hMN₂ : Scheme.Modules.IsInvertible (M ⊗ (Scheme.Modules.pullback q).obj N₂) := hM.tensor (hN₂.pullback q)
    rw [hMN₁.comap_zeroSchemeIdeal W.ι s₁, hMN₂.comap_zeroSchemeIdeal W.ι s₂,
      ← Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso (Scheme.Modules.pullbackSection W.ι s₁) φ₁.hom,
      ← Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso (Scheme.Modules.pullbackSection W.ι s₂) φ₂.hom]
    set t₁ := Scheme.Modules.pullbackSection W.ι s₁ ≫ φ₁.hom with ht₁
    set t₂ := Scheme.Modules.pullbackSection W.ι s₂ ≫ φ₂.hom with ht₂

    suffices hu : ∃ u : Γ((W : Scheme.{u}), ⊤), IsUnit u ∧
        t₂.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) = u • t₁.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) by
      obtain ⟨u, hu, h⟩ := hu
      exact Scheme.Modules.IsInvertible.zeroSchemeIdeal_eq_of_app_eq_smul (hM.pullback W.ι) t₁ t₂ u hu h

    let τ' : (Scheme.Modules.pushforward (q ∣_ V)).obj (M.restrict W.ι) ≅ 𝟙_ ((V : Scheme.{u})).Modules :=
      ((Scheme.Modules.pushforwardRestrictIso q V).app M) ≪≫ τP
    let θ : (Scheme.Modules.pullback W.ι).obj M ≅ M.restrict W.ι :=
      ((Scheme.Modules.restrictFunctorIsoPullback W.ι).app M).symm
    have hMW : Scheme.Modules.IsInvertible (M.restrict W.ι) := by
      refine ⟨fun w => ?_⟩
      obtain ⟨O, hwO, ⟨τO⟩⟩ := (hM.pullback W.ι).exists_trivialization w
      exact ⟨O, hwO, ⟨(Scheme.Modules.pullback O.ι).mapIso θ.symm ≪≫ τO⟩⟩

    have hsec : ∀ (i : Fin 2), True := fun _ => trivial
    have hs' : ∀ {L : (pullback c t).Modules} (sL : 𝟙_ _ ⟶ L) {dd : ℕ} (DD : RelEffCartierDiv c dd t)
        (hDDU : DD.SupportedIn U)
        (hZ : Scheme.Modules.zeroSchemeIdeal sL = DD.I) (hL : Scheme.Modules.IsInvertible L)
        (φ : (Scheme.Modules.pullback W.ι).obj L ≅ (Scheme.Modules.pullback W.ι).obj M),
        ∀ v : ↥V, ∃ w : ↥W, (q ∣_ V).base w = v ∧
          w ∉ (Scheme.Modules.zeroSchemeIdeal ((Scheme.Modules.pullbackSection W.ι sL ≫ φ.hom) ≫ θ.hom)).support := by
      intro L sL dd DD hDDU hZ hL φ v
      obtain ⟨y, hy, hyD⟩ := RelEffCartierDiv.exists_snd_apply_eq_and_notMem_support_of_supportedIn c U t DD hDDU (v : T) (hne v)
      have hyW : y ∈ W := by
        show q.base y ∈ V
        rw [show q.base y = (v : T) from hy]; exact v.2
      refine ⟨⟨y, hyW⟩, Subtype.ext (by rw [morphismRestrict_base_coe]; exact hy), ?_⟩
      rw [Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso, Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso,
        ← hL.comap_zeroSchemeIdeal W.ι sL, hZ]
      intro hw
      apply hyD
      have := hw
      rw [Scheme.IdealSheafData.support_comap] at this
      exact this
    have hs'₁ := hs' s₁ D₁ hD₁U hZ₁ hMN₁ φ₁
    have hs'₂ := hs' s₂ D₂ hD₂U hZ₂ hMN₂ φ₂

    have hu₁ := K5aUnitWs13.isUnit_coord_of_forall_fibre (q ∣_ V) hMW τ' (t₁ ≫ θ.hom) hs'₁
    have hu₂ := K5aUnitWs13.isUnit_coord_of_forall_fibre (q ∣_ V) hMW τ' (t₂ ≫ θ.hom) hs'₂

    set m₁ : Γ((Scheme.Modules.pushforward (q ∣_ V)).obj (M.restrict W.ι), ⊤) :=
      (t₁ ≫ θ.hom).app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) with hm₁
    set m₂ : Γ((Scheme.Modules.pushforward (q ∣_ V)).obj (M.restrict W.ι), ⊤) :=
      (t₂ ≫ θ.hom).app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) with hm₂
    set a₁ : Γ((V : Scheme.{u}), ⊤) := Scheme.Modules.ofUnitSection ⊤ (τ'.hom.app ⊤ m₁) with ha₁
    set a₂ : Γ((V : Scheme.{u}), ⊤) := Scheme.Modules.ofUnitSection ⊤ (τ'.hom.app ⊤ m₂) with ha₂
    set e' : Γ((Scheme.Modules.pushforward (q ∣_ V)).obj (M.restrict W.ι), ⊤) :=
      τ'.inv.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) with he'
    have hcoord : ∀ m : Γ((Scheme.Modules.pushforward (q ∣_ V)).obj (M.restrict W.ι), ⊤),
        m = Scheme.Modules.ofUnitSection ⊤ (τ'.hom.app ⊤ m) • e' := by
      intro m
      have h1 : τ'.hom.app ⊤ m = Scheme.Modules.ofUnitSection ⊤ (τ'.hom.app ⊤ m) • Scheme.Modules.toUnitSection ⊤ 1 := by
        apply Scheme.Modules.ofUnitSection_injective
        rw [Scheme.Modules.ofUnitSection_smul, Scheme.Modules.ofUnitSection_toUnitSection, mul_one]
      have h2 : m = τ'.inv.app ⊤ (τ'.hom.app ⊤ m) := by
        rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id, Scheme.Modules.Hom.id_app]
        rfl
      calc m = τ'.inv.app ⊤ (τ'.hom.app ⊤ m) := h2
        _ = τ'.inv.app ⊤ (Scheme.Modules.ofUnitSection ⊤ (τ'.hom.app ⊤ m) • Scheme.Modules.toUnitSection ⊤ 1) := by
            rw [← h1]
        _ = _ := by rw [Scheme.Modules.Hom.app_smul]
    have hm₁e : m₁ = a₁ • e' := hcoord m₁
    have hm₂e : m₂ = a₂ • e' := hcoord m₂

    set r : Γ((V : Scheme.{u}), ⊤) := a₂ * ↑(hu₁.unit⁻¹) with hr
    have hm₂₁ : m₂ = r • m₁ := by
      rw [hm₂e, hm₁e, smul_smul, hr, mul_assoc, IsUnit.val_inv_mul, mul_one]

    have hm₂₁' : (t₂ ≫ θ.hom).app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) =
        (q ∣_ V).appTop r • (show Γ(M.restrict W.ι, ⊤) from (t₁ ≫ θ.hom).app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)) :=
      hm₂₁
    refine ⟨(q ∣_ V).appTop r, (hu₂.mul (Units.isUnit _)).map _, ?_⟩
    have ht : ∀ tt : 𝟙_ _ ⟶ (Scheme.Modules.pullback W.ι).obj M,
        tt.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) =
          θ.inv.app ⊤ ((tt ≫ θ.hom).app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)) := by
      intro tt
      rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]
    rw [ht t₂, ht t₁, hm₂₁', Scheme.Modules.Hom.app_smul]
  choose V hV hloc using key
  let 𝒰 : (pullback c t).OpenCover :=
    Scheme.Cover.mkOfCovers (↥(pullback c t)) (fun z => ((q ⁻¹ᵁ V z : (pullback c t).Opens) : Scheme.{u}))
      (fun z => (q ⁻¹ᵁ V z).ι)
      (fun y => ⟨y, ⟨y, hV y⟩, rfl⟩)
      (fun z => inferInstance)
  rw [← hZ₁, ← hZ₂]
  exact Scheme.IdealSheafData.eq_of_forall_comap_openCover_eq 𝒰 fun z => hloc z

end S_AlgebraicGeometry_RelPicard_relEffCartierDiv_I_eq_of_lineBundle_iso_tensor_pullback_of_supportedIn
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_relEffCartierDiv_I_eq_of_lineBundle_iso_tensor_pullback_of_supportedIn (solution)
