-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.FiniteBySections.isFinite_of_unit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/ae6cc652-20cc-50cb-b36d-f62726985199

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_FiniteBySections_isFinite_of_unit

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace MvPolynomial HomogeneousLocalization AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_FiniteBySections_isFinite_of_unit.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.resLE_comp_ι Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top_assoc Scheme.basicOpen_res Spec.map_inj IsProper Scheme.toSpecΓ_naturality_assoc Scheme.Hom isAffine_of_isAffineOpen_basicOpen SpecMap_preimage_basicOpen Proj.basicOpenIsoSpec Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc IsFinite QuasiCompact IsAffine Spec Spec.map Scheme.Opens.toSpecΓ_preimage_basicOpen Scheme Proj.awayι QuasiCompact.compactSpace_of_compactSpace Scheme.isNilpotent_iff_basicOpen_eq_bot Proj IsFinite.iff_isProper_and_isAffineHom Proj.awayι_preimage_basicOpen toSpecΓ_SpecMap_ΓSpecIso_inv IsProper.of_comp Proj.isAffineOpen_basicOpen Proj.basicOpen Scheme.basicOpen_mul IsAffineOpen Scheme.Modules Scheme.Opens Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Scheme.toSpecΓ_preimage_basicOpen Proj.iSup_basicOpen_eq_top Scheme.Hom.comp_preimage IsAffineHom Proj.awayToSection Proj.basicOpenIsoSpec_hom toSpecΓ Scheme.ΓSpecIso Scheme.Modules.ProjPresentation Scheme.Modules.FiniteBySections ProjSpace.π ProjSpace.irrelevant_le_span_X ProjSpace.X_mem_one ProjSpace.awayι_comp_π ProjSpace.ratio"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Hom.resLE_comp_ι Opens.toSpecΓ_SpecMap_presheaf_map_top_assoc mem_basicOpen basicOpen_res basicOpen_of_isUnit ringCatSheaf toSpecΓ_naturality_assoc Hom Γ empty isoSpec_hom Opens.toSpecΓ_SpecMap_appLE_assoc Opens.toSpecΓ_preimage_basicOpen isNilpotent_iff_basicOpen_eq_bot zeroLocus basicOpen basicOpen_mul Modules Opens Hom.appLE_map Hom.app_eq_appLE toSpecΓ_preimage_basicOpen Hom.comp_preimage Modules.map_smul ΓSpecIso toSpecΓ Modules.ProjPresentation Modules.FiniteBySections"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "presheaf Hom map_smul ProjPresentation FiniteBySections"
namespace FBSUnit
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

section Frames

variable {X : Scheme.{u}} (M : X.Modules)

abbrev resTop (s : Γ(M, ⊤)) (V : X.Opens) : Γ(M, V) :=
  M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op s

def IsFrameOn (s : Γ(M, ⊤)) (V : X.Opens) : Prop :=
  ∀ V' : X.Opens, V' ≤ V →
    Function.Bijective fun g : Γ(X, V') => g • (M.presheaf.map (homOfLE (le_top : V' ≤ ⊤)).op s : Γ(M, V'))

variable {M}

theorem resTop_map {s : Γ(M, ⊤)} {V W : X.Opens} (h : W ≤ V) :
    M.presheaf.map (homOfLE h).op (resTop M s V) = resTop M s W := by
  simp only [resTop, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  rfl

namespace IsFrameOn

variable {s t : Γ(M, ⊤)} {V W : X.Opens}

theorem mono (h : IsFrameOn M s V) (hWV : W ≤ V) : IsFrameOn M s W :=
  fun V' hV' => h V' (hV'.trans hWV)

theorem bijective (h : IsFrameOn M s V) :
    Function.Bijective fun g : Γ(X, V) => g • resTop M s V := h V le_rfl

theorem injective (h : IsFrameOn M s V) {g g' : Γ(X, V)}
    (hg : g • resTop M s V = g' • resTop M s V) : g = g' :=
  h.bijective.1 hg

theorem isUnit_of_eq_smul (hs : IsFrameOn M s V) (ht : IsFrameOn M t V) (g : Γ(X, V))
    (hg : resTop M t V = g • resTop M s V) : IsUnit g := by
  obtain ⟨g', hg'⟩ := ht.bijective.2 (resTop M s V)
  simp only at hg'
  rw [hg, ← mul_smul] at hg'
  have h1 : g' * g = 1 := hs.injective (hg'.trans (one_smul _ _).symm)
  exact isUnit_iff_exists_inv'.mpr ⟨g', h1⟩

end IsFrameOn

end Frames

section Chart

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) {N : ℕ}

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R
local notation "ℙ" => Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)

def algR (V : X.Opens) : R →+* Γ(X, V) :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop ≫ X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom

theorem map_algR {V W : X.Opens} (ι : W ⟶ V) (r : R) :
    X.presheaf.map ι.op (algR f V r) = algR f W r := by
  change ((((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop ≫ X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op) ≫
    X.presheaf.map ι.op).hom r) = _
  simp only [algR, Category.assoc, ← Functor.map_comp, ← op_comp]
  rfl

theorem algR_top (r : R) : algR f ⊤ r = f.appTop ((Scheme.ΓSpecIso (.of R)).inv r) := by
  simp only [algR, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  have : (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)) = 𝟙 _ := rfl
  rw [this, op_id, X.presheaf.map_id]; rfl

section ChartDefs
variable (t : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)) (i : Fin (N + 1))
  (V : X.Opens) (hle : V ≤ t ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i))

def chartRing (t : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)) (i : Fin (N + 1))
    (V : X.Opens) (hle : V ≤ t ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)) : Away 𝒜 (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) R) →+* Γ(X, V) :=
  (Proj.awayToSection 𝒜 (MvPolynomial.X i) ≫ t.appLE (Proj.basicOpen 𝒜 (MvPolynomial.X i)) V hle).hom

theorem chartRing_apply (z : Away 𝒜 (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) R)) :
    chartRing t i V hle z = t.appLE (Proj.basicOpen 𝒜 (MvPolynomial.X i)) V hle (Proj.awayToSection 𝒜 (MvPolynomial.X i) z) := rfl

theorem map_app_awayToSection (z : Away 𝒜 (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) R)) :
    X.presheaf.map (homOfLE hle).op (t.app (Proj.basicOpen 𝒜 (MvPolynomial.X i)) (Proj.awayToSection 𝒜 (MvPolynomial.X i) z))
      = chartRing t i V hle z := by
  rw [← ConcreteCategory.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]; rfl

theorem map_chartRing {W : X.Opens} (h : W ≤ V) (z : Away 𝒜 (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) R)) :
    X.presheaf.map (homOfLE h).op (chartRing t i V hle z) = chartRing t i W (h.trans hle) z := by
  rw [chartRing_apply, ← ConcreteCategory.comp_apply, Scheme.Hom.appLE_map t hle (homOfLE h).op]; rfl

include hle in

theorem fac : V.ι ≫ t = V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (chartRing t i V hle)) ≫
    Proj.awayι 𝒜 (MvPolynomial.X i) (ProjSpace.X_mem_one R N i) one_pos := by
  rw [← Scheme.Hom.resLE_comp_ι t hle, Proj.awayι]
  have h1 : t.resLE (Proj.basicOpen 𝒜 (MvPolynomial.X i)) V hle ≫ (Proj.basicOpenIsoSpec 𝒜 (MvPolynomial.X i) (ProjSpace.X_mem_one R N i) one_pos).hom
      = V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (chartRing t i V hle)) := by
    rw [Proj.basicOpenIsoSpec_hom]
    change t.resLE (Proj.basicOpen 𝒜 (MvPolynomial.X i)) V hle ≫ (Proj.basicOpen 𝒜 (MvPolynomial.X i)).toSpecΓ ≫ Spec.map (Proj.awayToSection 𝒜 (MvPolynomial.X i)) = _
    rw [← Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc, ← Spec.map_comp]
    rfl
  rw [← reassoc_of% h1, Iso.hom_inv_id_assoc]

include hle in

theorem chartRing_comp_algebraMap (hV : IsAffineOpen V) (ht : t ≫ ProjSpace.π R N = f) :
    (chartRing t i V hle).comp (algebraMap R _) = algR f V := by
  have h1 : V.ι ≫ f = V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ((chartRing t i V hle).comp (algebraMap R _))) := by
    rw [← ht, ← Category.assoc, fac t i V hle, Category.assoc, Category.assoc, ProjSpace.awayι_comp_π,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have h2 : V.ι ≫ f = V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algR f V)) := by
    simp only [algR, CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc]
    rw [Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top_assoc, ← Scheme.toSpecΓ_naturality_assoc,
      toSpecΓ_SpecMap_ΓSpecIso_inv (.of R), Category.comp_id]
  rw [h1] at h2
  haveI : IsIso V.toSpecΓ := by rw [← hV.isoSpec_hom]; infer_instance
  rw [cancel_epi] at h2
  have h3 := Spec.map_inj.mp h2
  exact congrArg CommRingCat.Hom.hom h3

include hle in
theorem chartRing_algebraMap (hV : IsAffineOpen V) (ht : t ≫ ProjSpace.π R N = f) (r : R) :
    chartRing t i V hle (algebraMap R _ r) = algR f V r := by
  rw [← chartRing_comp_algebraMap f t i V hle hV ht]; rfl

end ChartDefs

end Chart

section Pres

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} {M : X.Modules} {N : ℕ}
  (𝔓 : M.ProjPresentation f N) (i : Fin (N + 1)) (V : X.Opens)
  (hle : V ≤ 𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i))

include hle in
theorem isFrameOn : IsFrameOn M (𝔓.σ i) V := fun V' h => 𝔓.frame i V' (h.trans hle)

theorem chartRing_ratio_smul (l : Fin (N + 1)) :
    chartRing 𝔓.toProj i V hle (ProjSpace.ratio R N i l) • resTop M (𝔓.σ i) V = resTop M (𝔓.σ l) V := by
  have h := 𝔓.app_ratio_smul i l
  have h' := congrArg (M.presheaf.map (homOfLE hle).op) h
  rw [Modules.map_smul] at h'
  rw [← map_app_awayToSection 𝔓.toProj i V hle]
  refine Eq.trans ?_ (h'.trans ?_)
  · congr 1
    exact (resTop_map hle).symm
  · exact resTop_map hle

end Pres

section Unit

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} {N : ℕ}
  (𝔓 : Scheme.Modules.ProjPresentation (SheafOfModules.unit X.ringCatSheaf : X.Modules) f N)

def fn (i : Fin (N + 1)) : Γ(X, ⊤) := (show Γ(X, ⊤) from 𝔓.σ i)

def U (i : Fin (N + 1)) : X.Opens :=
  𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)

theorem resTop_unit (i : Fin (N + 1)) (V : X.Opens) :
    (show Γ(X, V) from resTop (SheafOfModules.unit X.ringCatSheaf : X.Modules) (𝔓.σ i) V)
      = X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (fn 𝔓 i) := rfl

theorem unit_smul (V : X.Opens) (a : Γ(X, V)) (m : Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), V)) :
    (show Γ(X, V) from (a • m)) = a * (show Γ(X, V) from m) := rfl

theorem isUnit_res (i : Fin (N + 1)) : IsUnit (X.presheaf.map (homOfLE (le_top : U 𝔓 i ≤ ⊤)).op (fn 𝔓 i)) := by
  obtain ⟨g, hg⟩ := (𝔓.frame i (U 𝔓 i) le_rfl).2
    (show Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), U 𝔓 i) from (1 : Γ(X, U 𝔓 i)))
  have hg' : g * X.presheaf.map (homOfLE (le_top : U 𝔓 i ≤ ⊤)).op (fn 𝔓 i) = 1 := hg
  exact IsUnit.of_mul_eq_one_right _ hg'

theorem U_le_basicOpen (i : Fin (N + 1)) : U 𝔓 i ≤ X.basicOpen (fn 𝔓 i) := by
  have h := X.basicOpen_of_isUnit (isUnit_res 𝔓 i)
  rw [Scheme.basicOpen_res] at h
  exact (le_inf_iff.mp h.ge).2

theorem iSup_U : (⨆ i, U 𝔓 i) = ⊤ := by
  have hcov : (⨆ i : Fin (N + 1), Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
      (MvPolynomial.X i)) = ⊤ :=
    Proj.iSup_basicOpen_eq_top _ _ (ProjSpace.irrelevant_le_span_X R N)
  refine top_le_iff.mp fun x _ => ?_
  have hx : 𝔓.toProj.base x ∈ (⨆ i : Fin (N + 1), Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
      (MvPolynomial.X i)) := by rw [hcov]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  exact Opens.mem_iSup.mpr ⟨i, hi⟩

theorem isLocalizationElem_eq (j i : Fin (N + 1)) :
    HomogeneousLocalization.Away.isLocalizationElem (𝒜 := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
      (ProjSpace.X_mem_one R N j) (ProjSpace.X_mem_one R N i) = ProjSpace.ratio R N j i := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.Away.isLocalizationElem, ProjSpace.ratio, Away.val_mk, pow_one]

theorem ι_preimage_U (j i : Fin (N + 1)) :
    (U 𝔓 j).ι ⁻¹ᵁ U 𝔓 i = (U 𝔓 j).ι ⁻¹ᵁ X.basicOpen (chartRing 𝔓.toProj j (U 𝔓 j) le_rfl (ProjSpace.ratio R N j i)) := by
  have h1 : (U 𝔓 j).ι ⁻¹ᵁ U 𝔓 i = ((U 𝔓 j).ι ≫ 𝔓.toProj) ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i) := by
    rw [Scheme.Hom.comp_preimage]; rfl
  rw [h1, fac 𝔓.toProj j (U 𝔓 j) le_rfl]
  simp only [Scheme.Hom.comp_preimage]
  rw [Proj.awayι_preimage_basicOpen _ (ProjSpace.X_mem_one R N j) one_pos (ProjSpace.X_mem_one R N i) one_pos,
    SpecMap_preimage_basicOpen, Scheme.Opens.toSpecΓ_preimage_basicOpen, isLocalizationElem_eq]
  rfl

theorem mem_U_of_mem (j i : Fin (N + 1)) (x : X) (hxj : x ∈ U 𝔓 j)
    (hx : x ∈ X.basicOpen (chartRing 𝔓.toProj j (U 𝔓 j) le_rfl (ProjSpace.ratio R N j i))) : x ∈ U 𝔓 i := by
  have h := ι_preimage_U 𝔓 j i
  have : (⟨x, hxj⟩ : U 𝔓 j) ∈ (U 𝔓 j).ι ⁻¹ᵁ X.basicOpen (chartRing 𝔓.toProj j (U 𝔓 j) le_rfl (ProjSpace.ratio R N j i)) := hx
  rw [← h] at this
  exact this

theorem basicOpen_eq_U (i : Fin (N + 1)) : X.basicOpen (fn 𝔓 i) = U 𝔓 i := by
  refine le_antisymm ?_ (U_le_basicOpen 𝔓 i)
  intro x hx
  have hxtop : x ∈ (⊤ : X.Opens) := trivial
  rw [← iSup_U 𝔓] at hxtop
  obtain ⟨j, hxj⟩ := Opens.mem_iSup.mp hxtop

  set t := chartRing 𝔓.toProj j (U 𝔓 j) le_rfl (ProjSpace.ratio R N j i) with ht
  have hts : t * X.presheaf.map (homOfLE (le_top : U 𝔓 j ≤ ⊤)).op (fn 𝔓 j)
      = X.presheaf.map (homOfLE (le_top : U 𝔓 j ≤ ⊤)).op (fn 𝔓 i) := by
    have h := chartRing_ratio_smul 𝔓 j (U 𝔓 j) le_rfl i
    exact h
  apply mem_U_of_mem 𝔓 j i x hxj
  have hxi : x ∈ X.basicOpen (X.presheaf.map (homOfLE (le_top : U 𝔓 j ≤ ⊤)).op (fn 𝔓 i)) := by
    rw [Scheme.basicOpen_res]; exact ⟨hxj, hx⟩
  rw [← hts, Scheme.basicOpen_mul] at hxi
  exact hxi.1

theorem isAffineOpen_U [IsAffineHom 𝔓.toProj] (i : Fin (N + 1)) : IsAffineOpen (U 𝔓 i) :=
  (Proj.isAffineOpen_basicOpen _ (MvPolynomial.X i) (ProjSpace.X_mem_one R N i) one_pos).preimage 𝔓.toProj

end Unit

section Affine

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} {N : ℕ}
  (𝔓 : Scheme.Modules.ProjPresentation (SheafOfModules.unit X.ringCatSheaf : X.Modules) f N)

def θ : MvPolynomial (Fin (N + 1)) R →+* Γ(X, ⊤) :=
  MvPolynomial.eval₂Hom ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom (fn 𝔓)

@[scoped simp] theorem θ_X (i : Fin (N + 1)) : θ 𝔓 (MvPolynomial.X i) = fn 𝔓 i := by simp [θ]

theorem θ_comp_C : (θ 𝔓).comp MvPolynomial.C = ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom := by
  ext r; simp [θ]

def ψ : X ⟶ Spec (.of (MvPolynomial (Fin (N + 1)) R)) :=
  X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (θ 𝔓))

theorem ψ_comp : ψ 𝔓 ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial (Fin (N + 1)) R)) = f := by
  rw [ψ, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, θ_comp_C]
  simp only [CommRingCat.ofHom_hom, Spec.map_comp]
  rw [← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

theorem ψ_preimage_basicOpen (b : MvPolynomial (Fin (N + 1)) R) :
    ψ 𝔓 ⁻¹ᵁ PrimeSpectrum.basicOpen b = X.basicOpen (θ 𝔓 b) := by
  rw [ψ, Scheme.Hom.comp_preimage, SpecMap_preimage_basicOpen, Scheme.toSpecΓ_preimage_basicOpen]
  rfl

theorem mem_basicOpen_iff (x : X) (b : MvPolynomial (Fin (N + 1)) R) :
    b ∉ (ψ 𝔓 x).asIdeal ↔ x ∈ X.basicOpen (θ 𝔓 b) := by
  rw [← PrimeSpectrum.mem_basicOpen]
  show x ∈ ψ 𝔓 ⁻¹ᵁ PrimeSpectrum.basicOpen b ↔ _
  rw [ψ_preimage_basicOpen]

include 𝔓 in
theorem span_eq_top [IsFinite 𝔓.toProj] : Ideal.span (Set.range (fn 𝔓)) = ⊤ := by
  classical

  haveI : IsProper f := by rw [← 𝔓.toProj_π]; infer_instance
  haveI : IsProper (ψ 𝔓 ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial (Fin (N + 1)) R))) := by
    rw [ψ_comp]; infer_instance
  haveI : IsProper (ψ 𝔓) := IsProper.of_comp (ψ 𝔓)
    (Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial (Fin (N + 1)) R)))
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (ψ 𝔓)

  have hZ : IsClosed (Set.range (ψ 𝔓).base) := (ψ 𝔓).isClosedMap.isClosed_range
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).mp hZ
  let J : Ideal (MvPolynomial (Fin (N + 1)) R) := Ideal.span (Set.range MvPolynomial.X)
  have hcover : ∀ x : X, ∃ i, x ∈ X.basicOpen (fn 𝔓 i) := by
    intro x
    have hxtop : x ∈ (⊤ : X.Opens) := trivial
    rw [← iSup_U 𝔓] at hxtop
    obtain ⟨j, hxj⟩ := Opens.mem_iSup.mp hxtop
    exact ⟨j, U_le_basicOpen 𝔓 j hxj⟩
  have hempty : PrimeSpectrum.zeroLocus (↑(I ⊔ J) : Set (MvPolynomial (Fin (N + 1)) R)) = ∅ := by
    rw [PrimeSpectrum.zeroLocus_sup, ← hI, Set.eq_empty_iff_forall_notMem]
    rintro _ ⟨⟨x, rfl⟩, hxJ⟩
    obtain ⟨i, hi⟩ := hcover x
    rw [PrimeSpectrum.mem_zeroLocus] at hxJ
    have hXi : (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) R) ∈ ((ψ 𝔓).base x).asIdeal :=
      hxJ (Ideal.subset_span ⟨i, rfl⟩)
    have := (mem_basicOpen_iff 𝔓 x (MvPolynomial.X i)).mpr (by rw [θ_X]; exact hi)
    exact this hXi
  have htop : I ⊔ J = ⊤ := PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp hempty
  obtain ⟨a, haI, b, hbJ, hab⟩ := Submodule.mem_sup.mp (htop ▸ Submodule.mem_top : (1 : MvPolynomial (Fin (N + 1)) R) ∈ I ⊔ J)

  have hnil : IsNilpotent (θ 𝔓 a) := by
    rw [Scheme.isNilpotent_iff_basicOpen_eq_bot, eq_bot_iff]
    intro x hx
    have hna := (mem_basicOpen_iff 𝔓 x a).mpr hx
    have hxZ : (ψ 𝔓).base x ∈ PrimeSpectrum.zeroLocus (↑I : Set (MvPolynomial (Fin (N + 1)) R)) := hI ▸ ⟨x, rfl⟩
    exact (hna ((PrimeSpectrum.mem_zeroLocus _ _).mp hxZ haI)).elim

  have hθb : θ 𝔓 b ∈ Ideal.span (Set.range (fn 𝔓)) := by
    have h1 : θ 𝔓 b ∈ Ideal.map (θ 𝔓) J := Ideal.mem_map_of_mem _ hbJ
    rw [Ideal.map_span, ← Set.range_comp] at h1
    have h2 : (θ 𝔓) ∘ MvPolynomial.X = fn 𝔓 := funext fun i => θ_X 𝔓 i
    rwa [h2] at h1
  have hunit : IsUnit (θ 𝔓 b) := by
    have : θ 𝔓 b = 1 - θ 𝔓 a := by rw [← map_one (θ 𝔓), ← hab, map_add]; ring
    rw [this]; exact hnil.isUnit_one_sub
  exact Ideal.eq_top_of_isUnit_mem _ hθb hunit

include 𝔓 in

theorem isFinite [IsFinite 𝔓.toProj] : IsFinite f := by
  haveI : IsProper f := by rw [← 𝔓.toProj_π]; infer_instance
  haveI : IsAffine X := isAffine_of_isAffineOpen_basicOpen (Set.range (fn 𝔓)) (span_eq_top 𝔓) (by
    rintro _ ⟨i, rfl⟩
    rw [basicOpen_eq_U]
    exact isAffineOpen_U 𝔓 i)
  exact IsFinite.iff_isProper_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩

end Affine

end

end AlgebraicGeometry.Scheme.Modules.FBSUnit
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_FiniteBySections_isFinite_of_unit.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_FiniteBySections_isFinite_of_unit.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_Modules_FiniteBySections_isFinite_of_unit.AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_FiniteBySections_isFinite_of_unit.AlgebraicGeometry.Scheme.Modules.FBSUnit"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_FiniteBySections_isFinite_of_unit.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_FiniteBySections_isFinite_of_unit.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_Modules_FiniteBySections_isFinite_of_unit.AlgebraicGeometry.Scheme.Modules"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_FiniteBySections_isFinite_of_unit.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_FiniteBySections_isFinite_of_unit.AlgebraicGeometry.Scheme"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_FiniteBySections_isFinite_of_unit.AlgebraicGeometry"

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    (h𝒪 : Scheme.Modules.FiniteBySections (SheafOfModules.unit X.ringCatSheaf : X.Modules) f) :
    IsFinite f := by
  obtain ⟨N, 𝔓, h𝔓⟩ := h𝒪
  exact AlgebraicGeometry.Scheme.Modules.FBSUnit.isFinite 𝔓

end S_AlgebraicGeometry_Scheme_Modules_FiniteBySections_isFinite_of_unit
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_FiniteBySections_isFinite_of_unit (solution)
