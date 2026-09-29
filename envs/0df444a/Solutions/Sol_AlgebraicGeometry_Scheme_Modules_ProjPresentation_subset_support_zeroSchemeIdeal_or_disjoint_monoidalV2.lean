-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.ProjPresentation.subset_support_zeroSchemeIdeal_or_disjoint_monoidalV2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/4966bcb4-e9bd-5901-891b-c1b3fd799c7b

import Mathlib
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroSchemeV2
import Theorems.Thm_AlgebraicGeometry_Scheme_subset_basicOpen_or_disjoint_of_isProper_of_isIrreducible_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isFrameOn_app_of_disjoint_support_zeroSchemeIdeal_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_subset_support_zeroSchemeIdeal_or_disjoint_monoidalV2

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Scheme.basicOpen_res Scheme.Modules.Hom.app_smul Surjective IsProper Proj.opensRange_awayι Scheme.Hom Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Spec Scheme Proj.awayι Scheme.Modules.Hom.id_app Proj Scheme.mem_zeroLocus_iff Proj.basicOpen Scheme.Modules Scheme.Opens Scheme.Hom.mem_opensRange Scheme.Opens.ι_image_top Scheme.IdealSheafData.mem_support_iff_of_mem Scheme.Modules.map_smul Scheme.IdealSheafData Scheme.Modules.IsInvertible ProjSpace.X_mem_one ProjSpace.affineOpenCover Scheme.Modules.zeroSchemeIdeal Scheme.Modules.IsInvertible.exists_restrict_iso Scheme.subset_basicOpen_or_disjoint_of_isProper_of_isIrreducible_monoidalV2 Scheme.Modules.IsInvertible.isFrameOn_app_of_disjoint_support_zeroSchemeIdeal_monoidalV2 Scheme.Modules.IsInvertible.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq_monoidalV2" namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "basicOpen_res Modules.Hom.app_smul basicOpen_of_isUnit Hom.id_app Hom Γ Modules.Hom.comp_app Modules.Hom topIso Modules.Hom.id_app affineOpenCover mem_zeroLocus_iff Hom.comp_app basicOpen Modules Opens Hom.mem_opensRange Opens.ι_image_top IdealSheafData.mem_support_iff_of_mem Modules.map_smul basicOpen_le restrict IdealSheafData Modules.IsInvertible Modules.zeroSchemeIdeal Modules.IsInvertible.exists_restrict_iso subset_basicOpen_or_disjoint_of_isProper_of_isIrreducible_monoidalV2 Modules.IsInvertible.isFrameOn_app_of_disjoint_support_zeroSchemeIdeal_monoidalV2 Modules.IsInvertible.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq_monoidalV2" end AlgebraicGeometry.Scheme
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme" in
alias AlgebraicGeometry.Scheme.subset_basicOpen_or_disjoint_of_isProper_of_isIrreducible := AlgebraicGeometry.Scheme.subset_basicOpen_or_disjoint_of_isProper_of_isIrreducible_monoidalV2
namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Scheme.basicOpen_res Scheme.Modules.Hom.app_smul Surjective IsProper Proj.opensRange_awayι Scheme.Hom Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Spec Scheme Proj.awayι Scheme.Modules.Hom.id_app Proj Scheme.mem_zeroLocus_iff Proj.basicOpen Scheme.Modules Scheme.Opens Scheme.Hom.mem_opensRange Scheme.Opens.ι_image_top Scheme.IdealSheafData.mem_support_iff_of_mem Scheme.Modules.map_smul Scheme.IdealSheafData Scheme.Modules.IsInvertible ProjSpace.X_mem_one ProjSpace.affineOpenCover Scheme.Modules.zeroSchemeIdeal Scheme.Modules.IsInvertible.exists_restrict_iso Scheme.subset_basicOpen_or_disjoint_of_isProper_of_isIrreducible_monoidalV2 Scheme.Modules.IsInvertible.isFrameOn_app_of_disjoint_support_zeroSchemeIdeal_monoidalV2 Scheme.Modules.IsInvertible.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq_monoidalV2" namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "basicOpen_res Modules.Hom.app_smul basicOpen_of_isUnit Hom.id_app Hom Γ Modules.Hom.comp_app Modules.Hom topIso Modules.Hom.id_app affineOpenCover mem_zeroLocus_iff Hom.comp_app basicOpen Modules Opens Hom.mem_opensRange Opens.ι_image_top IdealSheafData.mem_support_iff_of_mem Modules.map_smul basicOpen_le restrict IdealSheafData Modules.IsInvertible Modules.zeroSchemeIdeal Modules.IsInvertible.exists_restrict_iso subset_basicOpen_or_disjoint_of_isProper_of_isIrreducible_monoidalV2 Modules.IsInvertible.isFrameOn_app_of_disjoint_support_zeroSchemeIdeal_monoidalV2 Modules.IsInvertible.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq_monoidalV2" namespace Modules p2m_export "AlgebraicGeometry.Scheme.Modules" "Hom.app_smul presheaf Hom.comp_app Hom Hom.id_app restrict map_smul IsInvertible IsFrameOn ProjPresentation toUnitSection ofUnitSection ofUnitSection_toUnitSection ofUnitSection_injective ofUnitSection_map ofUnitSection_smul restrictSection coeff zeroSchemeIdeal IsInvertible.exists_restrict_iso IsInvertible.isFrameOn_app_of_disjoint_support_zeroSchemeIdeal_monoidalV2 IsInvertible.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq_monoidalV2" namespace IsInvertible p2m_export "AlgebraicGeometry.Scheme.Modules.IsInvertible" "exists_restrict_iso isFrameOn_app_of_disjoint_support_zeroSchemeIdeal_monoidalV2 coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq_monoidalV2" end AlgebraicGeometry.Scheme.Modules.IsInvertible
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.IsInvertible" in
alias AlgebraicGeometry.Scheme.Modules.IsInvertible.isFrameOn_app_of_disjoint_support_zeroSchemeIdeal := AlgebraicGeometry.Scheme.Modules.IsInvertible.isFrameOn_app_of_disjoint_support_zeroSchemeIdeal_monoidalV2
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.IsInvertible" in
alias AlgebraicGeometry.Scheme.Modules.IsInvertible.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq := AlgebraicGeometry.Scheme.Modules.IsInvertible.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq_monoidalV2

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_subset_support_zeroSchemeIdeal_or_disjoint_monoidalV2.AlgebraicGeometry"

open scoped CategoryTheory.MonObj

attribute [local instance] MvPolynomial.gradedAlgebra

namespace P2mWs11C3

p2m_open "AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_subset_support_zeroSchemeIdeal_or_disjoint_monoidalV2.AlgebraicGeometry.Scheme.Modules"

variable {X : Scheme.{u}} {M : X.Modules}

theorem map_app_one (s : 𝟙_ X.Modules ⟶ M) {U W : X.Opens} (i : W ⟶ U) :
    M.presheaf.map i.op (s.app U (toUnitSection U 1)) = s.app W (toUnitSection W 1) := by
  have nat := (s.mapPresheaf).naturality i.op
  have h1 := congrFun (congrArg (fun f => (ConcreteCategory.hom f : Γ(𝟙_ X.Modules, U) → Γ(M, W))) nat)
    (toUnitSection U 1)
  have hu : (𝟙_ X.Modules).presheaf.map i.op (toUnitSection U 1) = toUnitSection W 1 := by
    apply ofUnitSection_injective
    rw [ofUnitSection_map, ofUnitSection_toUnitSection, ofUnitSection_toUnitSection, map_one]
  change (s.mapPresheaf.app _) ((𝟙_ X.Modules).presheaf.map i.op (toUnitSection U 1)) =
    M.presheaf.map i.op ((s.mapPresheaf.app _) (toUnitSection U 1)) at h1
  rw [hu] at h1
  exact h1.symm

theorem isFrameOn_smul_of_isUnit {U : X.Opens} {σ : Γ(M, U)} {V : X.Opens} (h : IsFrameOn σ V)
    (W : X.Opens) (hWU : W ≤ U) (hWV : W ≤ V) (g : Γ(X, W)) (hg : IsUnit g) :
    IsFrameOn (g • M.presheaf.map (homOfLE hWU).op σ : Γ(M, W)) W := by
  intro W' hW'W _
  have e : M.presheaf.map (homOfLE hW'W).op (g • M.presheaf.map (homOfLE hWU).op σ) =
      X.presheaf.map (homOfLE hW'W).op g • M.presheaf.map (homOfLE (hW'W.trans hWU)).op σ := by
    rw [Scheme.Modules.map_smul]
    congr 1
    change (M.presheaf.map (homOfLE hWU).op ≫ M.presheaf.map (homOfLE hW'W).op) σ = _
    rw [← M.presheaf.map_comp]; rfl
  simp only [e]
  set g' := X.presheaf.map (homOfLE hW'W).op g with hg'
  have hg'u : IsUnit g' := hg.map _
  have hb := h (hW'W.trans hWU) (hW'W.trans hWV)
  have : (fun f : Γ(X, W') => f • (g' • M.presheaf.map (homOfLE (hW'W.trans hWU)).op σ)) =
      (fun f : Γ(X, W') => f • M.presheaf.map (homOfLE (hW'W.trans hWU)).op σ) ∘ (fun f => f * g') := by
    funext f
    simp only [Function.comp_apply, mul_smul]
  rw [this]
  exact hb.comp ⟨fun a b hab => hg'u.mul_left_injective hab,
    fun c => ⟨c * ↑hg'u.unit⁻¹, by
      show c * ↑hg'u.unit⁻¹ * g' = c
      rw [mul_assoc, IsUnit.val_inv_mul, mul_one]⟩⟩

end P2mWs11C3

open P2mWs11C3 _root_.AlgebraicGeometry.Scheme.Modules _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_subset_support_zeroSchemeIdeal_or_disjoint_monoidalV2.AlgebraicGeometry.Scheme.Modules in

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k)) [IsProper t]
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) {N : ℕ} (𝔓 : M.ProjPresentation t N)
    (Z : Set X) (hZ : IsClosed Z) (hZ' : IsIrreducible Z)
    (y : Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)) (hy : IsClosed ({y} : Set _))
    (hZy : Z ⊆ 𝔓.toProj.base ⁻¹' {y}) (s : 𝟙_ X.Modules ⟶ M) :
    Z ⊆ (Scheme.Modules.zeroSchemeIdeal s).support ∨ Disjoint Z (Scheme.Modules.zeroSchemeIdeal s).support := by

  obtain ⟨i, hyi⟩ : ∃ i : Fin (N + 1), y ∈ Proj.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i) := by
    let j : Fin (N + 1) := (ProjSpace.affineOpenCover k N).openCover.idx y
    have hc : y ∈ Set.range ((ProjSpace.affineOpenCover k N).openCover.f j).base :=
      (ProjSpace.affineOpenCover k N).openCover.covers y
    refine ⟨j, ?_⟩
    have h2 : y ∈ (Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)
        (MvPolynomial.X j) (ProjSpace.X_mem_one k N j) one_pos).opensRange :=
      Scheme.Hom.mem_opensRange.mpr hc
    rwa [Proj.opensRange_awayι] at h2
  set U : X.Opens := 𝔓.toProj ⁻¹ᵁ Proj.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i) with hU
  have hZU : Z ⊆ (U : Set X) := fun z hz => by
    show 𝔓.toProj.base z ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i)
    have : 𝔓.toProj.base z = y := hZy hz
    rw [this]; exact hyi

  have hσ : IsFrameOn (𝔓.σ i) U := fun W hWU hWV => 𝔓.frame i W hWV
  set s₁ : Γ(M, ⊤) := s.app ⊤ (toUnitSection ⊤ 1) with hs₁
  obtain ⟨g, hg⟩ := (hσ (le_top : U ≤ ⊤) le_rfl).2 (M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s₁)

  have keyA : ∀ x : X, x ∈ U → x ∉ (zeroSchemeIdeal s).support → x ∈ X.basicOpen g := by
    intro x hxU hxs
    let V : X.Opens := ⟨((zeroSchemeIdeal s).support : Set X)ᶜ, (zeroSchemeIdeal s).support.isClosed.isOpen_compl⟩
    have hV : Disjoint (V : Set X) (zeroSchemeIdeal s).support := disjoint_compl_left
    have hs1 : IsFrameOn s₁ V :=
      Scheme.Modules.IsInvertible.isFrameOn_app_of_disjoint_support_zeroSchemeIdeal hM s V hV
    let W : X.Opens := V ⊓ U
    have hxW : x ∈ W := ⟨hxs, hxU⟩
    have hgW : X.presheaf.map (homOfLE (inf_le_right : W ≤ U)).op g •
        M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (𝔓.σ i) =
        M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s₁ := by
      have := congrArg (M.presheaf.map (homOfLE (inf_le_right : W ≤ U)).op) hg
      rw [Scheme.Modules.map_smul] at this
      convert this using 2
      · change _ = (M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ M.presheaf.map (homOfLE _).op) _
        rw [← M.presheaf.map_comp]; rfl
      · change _ = (M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ M.presheaf.map (homOfLE _).op) _
        rw [← M.presheaf.map_comp]; rfl
    obtain ⟨h, hh⟩ := (hs1 (le_top : W ≤ ⊤) inf_le_left).2
      (M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (𝔓.σ i))
    have hunit : h * X.presheaf.map (homOfLE (inf_le_right : W ≤ U)).op g = 1 := by
      apply (hσ (le_top : W ≤ ⊤) inf_le_right).1
      change (h * _) • _ = (1 : Γ(X, W)) • _
      rw [mul_smul, hgW]
      exact hh.trans (one_smul _ _).symm
    have hu : IsUnit (X.presheaf.map (homOfLE (inf_le_right : W ≤ U)).op g) :=
      isUnit_iff_exists_inv'.mpr ⟨h, hunit⟩
    have := X.basicOpen_of_isUnit hu
    rw [Scheme.basicOpen_res] at this
    have hx' : x ∈ W ⊓ X.basicOpen g := by rw [this]; exact hxW
    exact hx'.2

  have keyB : ∀ x : X, x ∈ X.basicOpen g → x ∉ (zeroSchemeIdeal s).support := by
    intro x hxB hxs
    set B : X.Opens := X.basicOpen g with hB
    have hBU : B ≤ U := X.basicOpen_le g
    have hsB : IsFrameOn (M.presheaf.map (homOfLE (le_top : B ≤ ⊤)).op s₁) B := by
      have hfr := isFrameOn_smul_of_isUnit hσ B (le_top : B ≤ ⊤) hBU (X.presheaf.map (homOfLE hBU).op g)
        (X.toRingedSpace.isUnit_res_basicOpen g)
      have e : X.presheaf.map (homOfLE hBU).op g • M.presheaf.map (homOfLE (le_top : B ≤ ⊤)).op (𝔓.σ i) =
          M.presheaf.map (homOfLE (le_top : B ≤ ⊤)).op s₁ := by
        have := congrArg (M.presheaf.map (homOfLE hBU).op) hg
        rw [Scheme.Modules.map_smul] at this
        convert this using 2
        · change _ = (M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ M.presheaf.map (homOfLE _).op) _
          rw [← M.presheaf.map_comp]; rfl
        · change _ = (M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ M.presheaf.map (homOfLE _).op) _
          rw [← M.presheaf.map_comp]; rfl
      rw [e] at hfr
      exact hfr
    have hs1B : IsFrameOn s₁ B := by
      intro W hWU hWB
      have := hsB hWB hWB
      have e : M.presheaf.map (homOfLE hWB).op (M.presheaf.map (homOfLE (le_top : B ≤ ⊤)).op s₁) =
          M.presheaf.map (homOfLE hWU).op s₁ := by
        change (M.presheaf.map _ ≫ M.presheaf.map _) _ = _
        rw [← M.presheaf.map_comp]; rfl
      rw [e] at this
      exact this
    obtain ⟨Ua, hxUa, hUaB, ⟨τ⟩⟩ := Scheme.Modules.IsInvertible.exists_restrict_iso hM (V := B) hxB
    have hfc := (Scheme.Modules.IsInvertible.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq hM s).2 Ua τ
    have hcu : IsUnit (coeff s Ua.1 τ.hom) := by
      have hle : Ua.1.ι ''ᵁ ⊤ ≤ B := by rw [Scheme.Opens.ι_image_top]; exact hUaB
      have hsurj := (hs1B (le_top : Ua.1.ι ''ᵁ ⊤ ≤ ⊤) hle).2
      have hr : restrictSection s Ua.1 = M.presheaf.map (homOfLE (le_top : Ua.1.ι ''ᵁ ⊤ ≤ ⊤)).op s₁ := by
        rw [hs₁, map_app_one]; rfl
      have hτs : Function.Surjective
          (τ.hom.app ⊤ : Γ(M.restrict Ua.1.ι, ⊤) → Γ(𝟙_ (Ua.1 : Scheme.{u}).Modules, ⊤)) := by
        intro m; refine ⟨τ.inv.app ⊤ m, ?_⟩
        change (τ.inv.app ⊤ ≫ τ.hom.app ⊤) m = m
        rw [← Scheme.Modules.Hom.comp_app, τ.inv_hom_id, Scheme.Modules.Hom.id_app]; rfl
      obtain ⟨m, hm⟩ := hτs (toUnitSection ⊤ 1)
      obtain ⟨f, hf⟩ := hsurj m
      have hf0 : f • (M.presheaf.map (homOfLE (le_top : Ua.1.ι ''ᵁ ⊤ ≤ ⊤)).op s₁) = m := hf
      set f' : Γ((Ua.1 : Scheme.{u}), ⊤) := (Ua.1.ι.appIso ⊤).hom f with hf'def
      have hlin : τ.hom.app ⊤ (f' • restrictSection s Ua.1) = f' • τ.hom.app ⊤ (restrictSection s Ua.1) :=
        Scheme.Modules.Hom.app_smul τ.hom f' _

      have hsm : f' • restrictSection s Ua.1 =
          f • @id (Γ(M, Ua.1.ι ''ᵁ ⊤)) (restrictSection s Ua.1) := by
        have e1 : f' • restrictSection s Ua.1 =
            ((Ua.1.ι.appIso ⊤).inv f') • @id (Γ(M, Ua.1.ι ''ᵁ ⊤)) (restrictSection s Ua.1) :=
          rfl
        rw [e1, hf'def, CategoryTheory.Iso.hom_inv_id_apply]
      have hf' : f' • restrictSection s Ua.1 = m := by
        rw [hsm, hr]
        exact hf0
      have h1 : f' * ofUnitSection ⊤ (τ.hom.app ⊤ (restrictSection s Ua.1)) = 1 := by
        have h2 : τ.hom.app ⊤ m = toUnitSection ⊤ 1 := hm
        rw [← hf', hlin] at h2
        have h3 := congrArg (ofUnitSection ⊤) h2
        rw [ofUnitSection_smul, ofUnitSection_toUnitSection] at h3
        exact h3
      have hc : IsUnit (ofUnitSection ⊤ (τ.hom.app ⊤ (restrictSection s Ua.1))) :=
        isUnit_iff_exists_inv'.mpr ⟨_, h1⟩
      change IsUnit (Ua.1.topIso.hom (ofUnitSection ⊤ (τ.hom.app ⊤ (restrictSection s Ua.1))))
      exact hc.map _
    have hideal : (zeroSchemeIdeal s).ideal Ua = ⊤ := by
      rw [hfc.1, Ideal.span_singleton_eq_top]; exact hcu
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := Ua) hxUa, Scheme.mem_zeroLocus_iff] at hxs
    have := hxs 1 (by rw [hideal]; trivial)
    rw [X.basicOpen_of_isUnit isUnit_one] at this
    exact this hxUa

  rcases AlgebraicGeometry.Scheme.subset_basicOpen_or_disjoint_of_isProper_of_isIrreducible
      k t Z hZ hZ' U hZU g with h | h
  · right
    rw [Set.disjoint_left]
    intro z hz hzs
    exact keyB z (h hz) hzs
  · left
    intro z hz
    by_contra hzs
    exact Set.disjoint_left.mp h hz (keyA z (hZU hz) hzs)

end S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_subset_support_zeroSchemeIdeal_or_disjoint_monoidalV2
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_subset_support_zeroSchemeIdeal_or_disjoint_monoidalV2 (solution)
