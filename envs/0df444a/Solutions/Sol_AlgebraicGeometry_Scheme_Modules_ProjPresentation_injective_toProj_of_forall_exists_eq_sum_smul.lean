-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.ProjPresentation.injective_toProj_of_forall_exists_eq_sum_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/04754240-5def-5c42-972c-7e9ca5da8b48

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_algHom_away_apply_ratio_eq
import Theorems.Thm_AlgebraicGeometry_Proj_basicOpen_mul_eq_basicOpen_awayToSection
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_injective_toProj_of_forall_exists_eq_sum_smul

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace MvPolynomial HomogeneousLocalization AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_injective_toProj_of_forall_exists_eq_sum_smul.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.resLE_comp_ι Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top_assoc Spec.map_inj Scheme.toSpecΓ_naturality_assoc Scheme.Hom Proj.basicOpenIsoSpec Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc Spec Spec.map RingedSpace.isUnit_res_basicOpen Scheme Proj.awayι Scheme.Hom.comp_base Proj Scheme.basicOpen_appLE toSpecΓ_SpecMap_ΓSpecIso_inv Scheme.Opens.ι_apply Proj.basicOpen Proj.basicOpen_mul IsAffineOpen Scheme.Modules Scheme.Opens Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Proj.iSup_basicOpen_eq_top Proj.awayToSection Proj.basicOpenIsoSpec_hom toSpecΓ RingedSpace Scheme.ΓSpecIso ProjSpace.π ProjSpace.irrelevant_le_span_X ProjSpace.X_mem_one ProjSpace.awayι_comp_π ProjSpace.ratio ProjSpace.adjoin_range_ratio ProjSpace.exists_algHom_away_apply_ratio_eq Proj.basicOpen_mul_eq_basicOpen_awayToSection"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Hom.resLE_comp_ι Opens.toSpecΓ_SpecMap_presheaf_map_top_assoc basicOpen_of_isUnit toSpecΓ_naturality_assoc Hom Γ isoSpec_hom Opens.toSpecΓ_SpecMap_appLE_assoc toLocallyRingedSpace Hom.comp_base basicOpen basicOpen_appLE Opens.ι_apply basicOpen_mul isBasis_affineOpens Modules Opens Hom.appLE_map Hom.app_eq_appLE Modules.map_smul basicOpen_le ΓSpecIso toSpecΓ"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "presheaf Hom map_smul ProjPresentation"
namespace D2INJ
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

section Aux

variable {X : Scheme.{u}} {M : X.Modules}

theorem IsFrameOn.of_eq_unit_smul {s t : Γ(M, ⊤)} {V : X.Opens} (ht : IsFrameOn M t V) (g : Γ(X, V)) (hg : IsUnit g)
    (h : resTop M s V = g • resTop M t V) : IsFrameOn M s V := by
  intro V' hV'
  have h' : resTop M s V' = X.presheaf.map (homOfLE hV').op g • resTop M t V' := by
    rw [← resTop_map hV', h, Modules.map_smul, resTop_map hV']
  have hg' : IsUnit (X.presheaf.map (homOfLE hV').op g) := hg.map _
  have e1 : (fun a : Γ(X, V') => a • (M.presheaf.map (homOfLE (le_top : V' ≤ ⊤)).op s : Γ(M, V'))) =
      (fun a : Γ(X, V') => a • resTop M t V') ∘ (fun a => a * X.presheaf.map (homOfLE hV').op g) := by
    funext a
    show a • resTop M s V' = (a * X.presheaf.map (homOfLE hV').op g) • resTop M t V'
    rw [h', mul_smul]
  rw [e1]
  exact (ht V' hV').comp ⟨hg'.mul_left_injective, fun b => ⟨b * ↑hg'.unit⁻¹, by
    show b * ↑hg'.unit⁻¹ * X.presheaf.map (homOfLE hV').op g = b
    rw [mul_assoc, hg'.val_inv_mul, mul_one]⟩⟩

theorem isUnit_of_basicOpen_eq {U : X.Opens} (s : Γ(X, U)) (h : X.basicOpen s = U) : IsUnit s := by
  have h1 := RingedSpace.isUnit_res_basicOpen X.toLocallyRingedSpace.toRingedSpace s
  let ι1 : op U ⟶ op (X.basicOpen s) := (homOfLE (X.basicOpen_le s)).op
  let ι2 : op (X.basicOpen s) ⟶ op U := eqToHom (congrArg op h)
  have hcomp : X.presheaf.map ι1 ≫ X.presheaf.map ι2 = 𝟙 _ := by
    rw [← X.presheaf.map_comp, show ι1 ≫ ι2 = 𝟙 _ from Subsingleton.elim _ _, X.presheaf.map_id]
  have hs : s = X.presheaf.map ι2 (X.presheaf.map ι1 s) := by
    rw [← CommRingCat.comp_apply, hcomp]; rfl
  rw [hs]
  exact h1.map _

theorem base_apply_eq_of_fac {Y Z W : Scheme.{u}} {V : X.Opens} {t : X ⟶ Y} {a : (V : Scheme.{u}) ⟶ Z} {b : Z ⟶ W} {c : W ⟶ Y}
    (hfac : V.ι ≫ t = a ≫ b ≫ c) (x : X) (hx : x ∈ V) :
    t.base x = c.base (b.base (a.base ⟨x, hx⟩)) := by
  have := congrArg (fun φ : (V : Scheme.{u}) ⟶ Y => φ.base ⟨x, hx⟩) hfac
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at this
  rw [← this]
  exact (congrArg t.base (Scheme.Opens.ι_apply V ⟨x, hx⟩)).symm

end Aux

section Inj

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} {M : X.Modules} {N N' : ℕ}
  (𝔓 : M.ProjPresentation f N) (𝔔 : M.ProjPresentation f N')

local notation "𝒜P" => MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R
local notation "𝒜Q" => MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) R

def aCoef (j : Fin (N' + 1)) (c : Fin (N + 1) → Fin (N' + 1) → R) (l : Fin (N + 1)) :
    Away 𝒜Q (MvPolynomial.X j : MvPolynomial (Fin (N' + 1)) R) :=
  ∑ k, algebraMap R _ (c l k) * ProjSpace.ratio R N' j k

theorem chartRing_aCoef_smul (j : Fin (N' + 1)) (c : Fin (N + 1) → Fin (N' + 1) → R)
    (V : X.Opens) (hV : IsAffineOpen V)
    (hVj : V ≤ 𝔔.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) R) (MvPolynomial.X j))
    (hc : ∀ l, resTop M (𝔓.σ l) V = ∑ k, algR f V (c l k) • resTop M (𝔔.σ k) V) (l : Fin (N + 1)) :
    chartRing 𝔔.toProj j V hVj (aCoef j c l) • resTop M (𝔔.σ j) V = resTop M (𝔓.σ l) V := by
  simp only [aCoef, map_sum, map_mul, Finset.sum_smul, mul_smul]
  rw [hc l]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [chartRing_algebraMap f 𝔔.toProj j V hVj hV 𝔔.toProj_π, chartRing_ratio_smul 𝔔 j V hVj k]

theorem isUnit_chartRing_aCoef (i : Fin (N + 1)) (j : Fin (N' + 1)) (c : Fin (N + 1) → Fin (N' + 1) → R)
    (V : X.Opens) (hV : IsAffineOpen V)
    (hVi : V ≤ 𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i))
    (hVj : V ≤ 𝔔.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) R) (MvPolynomial.X j))
    (hc : ∀ l, resTop M (𝔓.σ l) V = ∑ k, algR f V (c l k) • resTop M (𝔔.σ k) V) : IsUnit (chartRing 𝔔.toProj j V hVj (aCoef j c i)) :=
  (isFrameOn 𝔔 j V hVj).isUnit_of_eq_smul (isFrameOn 𝔓 i V hVi) _ (chartRing_aCoef_smul 𝔓 𝔔 j c V hV hVj hc i).symm

theorem chartRing_eq_comp (i : Fin (N + 1)) (j : Fin (N' + 1)) (c : Fin (N + 1) → Fin (N' + 1) → R)
    (V : X.Opens) (hV : IsAffineOpen V)
    (hVi : V ≤ 𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i))
    (hVj : V ≤ 𝔔.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) R) (MvPolynomial.X j))
    (hc : ∀ l, resTop M (𝔓.σ l) V = ∑ k, algR f V (c l k) • resTop M (𝔔.σ k) V)
    (γ : Away 𝒜P (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) R) →ₐ[R] Localization.Away (aCoef (N := N) j c i))
    (hγ : ∀ l, γ (ProjSpace.ratio R N i l) =
      algebraMap _ (Localization.Away (aCoef (N := N) j c i)) (aCoef j c l) * IsLocalization.Away.invSelf (aCoef (N := N) j c i))
    (hu : IsUnit (chartRing 𝔔.toProj j V hVj (aCoef j c i))) :
    chartRing 𝔓.toProj i V hVi =
      (IsLocalization.Away.lift (S := Localization.Away (aCoef (N := N) j c i)) (aCoef j c i)
        (g := chartRing 𝔔.toProj j V hVj) hu).comp γ.toRingHom := by
  classical
  set α := chartRing 𝔓.toProj i V hVi with hαdef
  set β := chartRing 𝔔.toProj j V hVj with hβdef
  let Ay := Away 𝒜Q (MvPolynomial.X j : MvPolynomial (Fin (N' + 1)) R)
  let a : Fin (N + 1) → Ay := aCoef j c
  have hβa : ∀ l, β (a l) • resTop M (𝔔.σ j) V = resTop M (𝔓.σ l) V := chartRing_aCoef_smul 𝔓 𝔔 j c V hV hVj hc
  have hFj : IsFrameOn M (𝔔.σ j) V := isFrameOn 𝔔 j V hVj
  have hαr : ∀ l, α (ProjSpace.ratio R N i l) * β (a i) = β (a l) := by
    intro l
    apply hFj.injective
    show (α (ProjSpace.ratio R N i l) * β (a i)) • resTop M (𝔔.σ j) V = β (a l) • resTop M (𝔔.σ j) V
    rw [mul_smul, hβa i, hαdef, chartRing_ratio_smul 𝔓 i V hVi l, hβa l]
  let βt : Localization.Away (a i) →+* Γ(X, V) :=
    IsLocalization.Away.lift (S := Localization.Away (a i)) (a i) (g := β) hu
  have hβt' : ∀ y, βt (algebraMap Ay (Localization.Away (a i)) y) = β y := fun y =>
    IsLocalization.Away.lift_eq (S := Localization.Away (a i)) (a i) hu y
  have algRB_apply : ∀ r, algebraMap R (Localization.Away (a i)) r
      = algebraMap Ay (Localization.Away (a i)) (algebraMap R Ay r) := fun r =>
    IsScalarTower.algebraMap_apply R Ay (Localization.Away (a i)) r
  letI algRV : Algebra R Γ(X, V) := (β.comp (algebraMap R Ay)).toAlgebra
  have algRV_apply : ∀ r, algebraMap R Γ(X, V) r = β (algebraMap R Ay r) := fun r => rfl
  have hαβR : ∀ r, α (algebraMap R _ r) = β (algebraMap R Ay r) := fun r =>
    (chartRing_algebraMap f 𝔓.toProj i V hVi hV 𝔓.toProj_π r).trans
      (chartRing_algebraMap f 𝔔.toProj j V hVj hV 𝔔.toProj_π r).symm
  let αA : Away 𝒜P (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) R) →ₐ[R] Γ(X, V) :=
    { α with
      commutes' := fun r => by
        rw [algRV_apply]
        exact hαβR r }
  let βtA : Localization.Away (a i) →ₐ[R] Γ(X, V) :=
    { βt with
      commutes' := fun r => by
        rw [algRB_apply, algRV_apply]
        exact hβt' _ }
  have hinv : βt (IsLocalization.Away.invSelf (a i)) * β (a i) = 1 := by
    rw [← hβt' (a i), ← map_mul, mul_comm]
    exact (congrArg βt (IsLocalization.Away.mul_invSelf (S := Localization.Away (a i)) (a i))).trans (map_one βt)
  have hAlg : αA = βtA.comp γ := by
    apply AlgHom.ext_of_adjoin_eq_top (ProjSpace.adjoin_range_ratio R N i)
    rintro _ ⟨l, rfl⟩
    show α (ProjSpace.ratio R N i l) = βt (γ (ProjSpace.ratio R N i l))
    rw [hγ, map_mul, hβt']
    calc α (ProjSpace.ratio R N i l)
        = α (ProjSpace.ratio R N i l) * (βt (IsLocalization.Away.invSelf (a i)) * β (a i)) := by
          rw [hinv, mul_one]
      _ = (α (ProjSpace.ratio R N i l) * β (a i)) * βt (IsLocalization.Away.invSelf (a i)) := by ring
      _ = β (a l) * βt (IsLocalization.Away.invSelf (a i)) := by rw [hαr]
  exact congrArg AlgHom.toRingHom hAlg

theorem hc_res' (c : Fin (N + 1) → Fin (N' + 1) → R) (hc0 : ∀ l, 𝔓.σ l = ∑ k, (f.appTop ((Scheme.ΓSpecIso (.of R)).inv (c l k))) • 𝔔.σ k) (W : X.Opens)
    (l : Fin (N + 1)) : resTop M (𝔓.σ l) W = ∑ k, algR f W (c l k) • resTop M (𝔔.σ k) W := by
  have h := congrArg (M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op) (hc0 l)
  rw [map_sum] at h
  refine h.trans (Finset.sum_congr rfl fun k _ => ?_)
  rw [Modules.map_smul]
  rfl

theorem isLocalizationElem_eq_ratio (k i : Fin (N + 1)) :
    HomogeneousLocalization.Away.isLocalizationElem (ProjSpace.X_mem_one R N k) (ProjSpace.X_mem_one R N i) =
      ProjSpace.ratio R N k i := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.Away.isLocalizationElem, ProjSpace.ratio, HomogeneousLocalization.Away.val_mk, pow_one]

end Inj

end

end AlgebraicGeometry.Scheme.Modules.D2INJ

open AlgebraicGeometry.Scheme.Modules.D2INJ in
attribute [local instance] MvPolynomial.gradedAlgebra in
theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} {M : X.Modules} {N N' : ℕ}
    (𝔓 : M.ProjPresentation f N) (𝔔 : M.ProjPresentation f N') (hinj : Function.Injective 𝔓.toProj.base)
    (h : ∀ i : Fin (N + 1), ∃ c : Fin (N' + 1) → R,
      𝔓.σ i = ∑ j, (f.appTop ((Scheme.ΓSpecIso (.of R)).inv (c j))) • 𝔔.σ j) :
    Function.Injective 𝔔.toProj.base := by
  classical
  choose c hc using h
  intro x x' hxx'

  have hcovP : (⨆ i : Fin (N + 1), Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
      (MvPolynomial.X i)) = ⊤ := Proj.iSup_basicOpen_eq_top _ _ (ProjSpace.irrelevant_le_span_X R N)
  have hcovQ : (⨆ j : Fin (N' + 1), Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) R)
      (MvPolynomial.X j)) = ⊤ := Proj.iSup_basicOpen_eq_top _ _ (ProjSpace.irrelevant_le_span_X R N')
  have hxP : 𝔓.toProj.base x ∈ (⨆ i : Fin (N + 1), Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
      (MvPolynomial.X i)) := by rw [hcovP]; trivial
  have hx'P : 𝔓.toProj.base x' ∈ (⨆ i : Fin (N + 1), Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
      (MvPolynomial.X i)) := by rw [hcovP]; trivial
  have hxQ : 𝔔.toProj.base x ∈ (⨆ j : Fin (N' + 1), Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) R)
      (MvPolynomial.X j)) := by rw [hcovQ]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hxP
  obtain ⟨k, hk⟩ := Opens.mem_iSup.mp hx'P
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hxQ
  have hj' : x' ∈ 𝔔.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) R) (MvPolynomial.X j) := by
    show 𝔔.toProj.base x' ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) R) (MvPolynomial.X j)
    rw [← hxx']; exact hj

  obtain ⟨_, ⟨V, hVaff, rfl⟩, hxV, hVW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (a := x)
    (show x ∈ ((𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)) ⊓
      (𝔔.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) R) (MvPolynomial.X j)) : X.Opens)
      from ⟨hi, hj⟩) (Opens.isOpen _)
  have hVi : V ≤ 𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i) :=
    fun p hp => (hVW hp).1
  have hVj : V ≤ 𝔔.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) R) (MvPolynomial.X j) :=
    fun p hp => (hVW hp).2
  have huV := isUnit_chartRing_aCoef 𝔓 𝔔 i j c V hVaff hVi hVj (hc_res' 𝔓 𝔔 c hc V)

  let G : (Proj (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) R)).Opens :=
    (Proj (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) R)).basicOpen
      (Proj.awayToSection _ (MvPolynomial.X j) (aCoef (N := N) j c i))
  have hbo : X.basicOpen (chartRing 𝔔.toProj j V hVj (aCoef (N := N) j c i)) = V ⊓ 𝔔.toProj ⁻¹ᵁ G := by
    rw [chartRing_apply, Scheme.basicOpen_appLE]
  have hxG : x ∈ 𝔔.toProj ⁻¹ᵁ G := by
    rw [X.basicOpen_of_isUnit huV] at hbo
    exact (hbo.le hxV).2
  have hx'G : x' ∈ 𝔔.toProj ⁻¹ᵁ G := by show 𝔔.toProj.base x' ∈ G; rw [← hxx']; exact hxG

  obtain ⟨_, ⟨V', hV'aff, rfl⟩, hx'V', hV'W⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (a := x')
    (show x' ∈ (((𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X k)) ⊓
      (𝔔.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) R) (MvPolynomial.X j))) ⊓
      (𝔔.toProj ⁻¹ᵁ G) : X.Opens) from ⟨⟨hk, hj'⟩, hx'G⟩) (Opens.isOpen _)
  have hV'k : V' ≤ 𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X k) :=
    fun p hp => (hV'W hp).1.1
  have hV'j : V' ≤ 𝔔.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) R) (MvPolynomial.X j) :=
    fun p hp => (hV'W hp).1.2
  have hV'G : V' ≤ 𝔔.toProj ⁻¹ᵁ G := fun p hp => (hV'W hp).2

  have huV' : IsUnit (chartRing 𝔔.toProj j V' hV'j (aCoef (N := N) j c i)) := by
    apply isUnit_of_basicOpen_eq
    rw [chartRing_apply, Scheme.basicOpen_appLE]
    exact inf_eq_left.mpr hV'G
  have hFi' : IsFrameOn M (𝔓.σ i) V' :=
    IsFrameOn.of_eq_unit_smul (isFrameOn 𝔔 j V' hV'j) _ huV'
      (chartRing_aCoef_smul 𝔓 𝔔 j c V' hV'aff hV'j (hc_res' 𝔓 𝔔 c hc V') i).symm
  have hunit2 : IsUnit (chartRing 𝔓.toProj k V' hV'k (ProjSpace.ratio R N k i)) :=
    (isFrameOn 𝔓 k V' hV'k).isUnit_of_eq_smul hFi' _ (chartRing_ratio_smul 𝔓 k V' hV'k i).symm
  have hx'i : x' ∈ 𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i) := by
    have hb2 : X.basicOpen (chartRing 𝔓.toProj k V' hV'k (ProjSpace.ratio R N k i)) =
        V' ⊓ 𝔓.toProj ⁻¹ᵁ (Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)).basicOpen
          (Proj.awayToSection _ (MvPolynomial.X k) (ProjSpace.ratio R N k i)) := by
      rw [chartRing_apply, Scheme.basicOpen_appLE]
    rw [X.basicOpen_of_isUnit hunit2, ← isLocalizationElem_eq_ratio,
      ← AlgebraicGeometry.Proj.basicOpen_mul_eq_basicOpen_awayToSection _ (ProjSpace.X_mem_one R N k) one_pos
        (ProjSpace.X_mem_one R N i) one_pos, Proj.basicOpen_mul] at hb2
    exact ((hb2.le hx'V').2).2

  obtain ⟨_, ⟨V'', hV''aff, rfl⟩, hx'V'', hV''W⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (a := x')
    (show x' ∈ ((𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)) ⊓
      (𝔔.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) R) (MvPolynomial.X j)) : X.Opens)
      from ⟨hx'i, hj'⟩) (Opens.isOpen _)
  have hV''i : V'' ≤ 𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i) :=
    fun p hp => (hV''W hp).1
  have hV''j : V'' ≤ 𝔔.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) R) (MvPolynomial.X j) :=
    fun p hp => (hV''W hp).2
  have huV'' := isUnit_chartRing_aCoef 𝔓 𝔔 i j c V'' hV''aff hV''i hV''j (hc_res' 𝔓 𝔔 c hc V'')

  obtain ⟨γ, hγ⟩ := ProjSpace.exists_algHom_away_apply_ratio_eq R N i (B := Localization.Away (aCoef (N := N) j c i))
    (fun l => algebraMap _ (Localization.Away (aCoef (N := N) j c i)) (aCoef j c l) *
      IsLocalization.Away.invSelf (aCoef (N := N) j c i))
    (by exact IsLocalization.Away.mul_invSelf (aCoef (N := N) j c i))
  have hfacV := chartRing_eq_comp 𝔓 𝔔 i j c V hVaff hVi hVj (hc_res' 𝔓 𝔔 c hc V) γ hγ huV
  have hfacV'' := chartRing_eq_comp 𝔓 𝔔 i j c V'' hV''aff hV''i hV''j (hc_res' 𝔓 𝔔 c hc V'') γ hγ huV''

  have ePx := base_apply_eq_of_fac (fac 𝔓.toProj i V hVi) x hxV
  have ePx' := base_apply_eq_of_fac (fac 𝔓.toProj i V'' hV''i) x' hx'V''
  have eQx := base_apply_eq_of_fac (fac 𝔔.toProj j V hVj) x hxV
  have eQx' := base_apply_eq_of_fac (fac 𝔔.toProj j V'' hV''j) x' hx'V''
  apply hinj
  rw [ePx, ePx', hfacV, hfacV'', CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp]
  simp only [Scheme.Hom.comp_base, TopCat.comp_app]
  congr 2

  apply (Spec.map (CommRingCat.ofHom (algebraMap (Away (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) R) (MvPolynomial.X j : MvPolynomial (Fin (N' + 1)) R))
    (Localization.Away (aCoef (N := N) j c i))))).isOpenEmbedding.injective
  have eβ : ∀ (W : X.Opens)
      (hWj : W ≤ 𝔔.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) R) (MvPolynomial.X j))
      (hu : IsUnit (chartRing 𝔔.toProj j W hWj (aCoef (N := N) j c i))) (p : (W : Scheme.{u})),
      (Spec.map (CommRingCat.ofHom (algebraMap _ (Localization.Away (aCoef (N := N) j c i))))).base
        ((Spec.map (CommRingCat.ofHom (IsLocalization.Away.lift (S := Localization.Away (aCoef (N := N) j c i))
          (aCoef j c i) (g := chartRing 𝔔.toProj j W hWj) hu))).base (W.toSpecΓ.base p))
      = (Spec.map (CommRingCat.ofHom (chartRing 𝔔.toProj j W hWj))).base (W.toSpecΓ.base p) := by
    intro W hWj hu p
    conv_rhs => rw [← IsLocalization.Away.lift_comp (S := Localization.Away (aCoef (N := N) j c i)) (aCoef j c i) hu,
      CommRingCat.ofHom_comp, Spec.map_comp, Scheme.Hom.comp_base, TopCat.comp_app]
  rw [eβ V hVj huV, eβ V'' hV''j huV'']
  apply (Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) R) (MvPolynomial.X j) (ProjSpace.X_mem_one R N' j)
    one_pos).isOpenEmbedding.injective
  rw [← eQx, ← eQx']
  exact hxx'

end S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_injective_toProj_of_forall_exists_eq_sum_smul
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_injective_toProj_of_forall_exists_eq_sum_smul (solution)
