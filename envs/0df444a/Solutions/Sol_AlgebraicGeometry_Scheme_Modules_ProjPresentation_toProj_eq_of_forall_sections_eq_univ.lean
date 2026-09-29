-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.ProjPresentation.toProj_eq_of_forall_sections_eq_univ
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/08acbe90-8532-588c-bb6e-c6d3965bf551

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_mem_preimage_basicOpen_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_toProj_eq_of_forall_sections_eq_univ

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace MvPolynomial HomogeneousLocalization AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_toProj_eq_of_forall_sections_eq_univ.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.resLE_comp_ι Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top_assoc Spec.map_inj Scheme.toSpecΓ_naturality_assoc Scheme.Hom Proj.basicOpenIsoSpec Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc Spec Spec.map Scheme Proj.awayι Proj toSpecΓ_SpecMap_ΓSpecIso_inv Proj.basicOpen IsAffineOpen Scheme.Modules Scheme.Opens Scheme.hom_ext_of_forall Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Proj.iSup_basicOpen_eq_top Proj.awayToSection Proj.basicOpenIsoSpec_hom toSpecΓ Scheme.ΓSpecIso ProjSpace.π ProjSpace.irrelevant_le_span_X ProjSpace.X_mem_one ProjSpace.awayι_comp_π ProjSpace.ratio ProjSpace.adjoin_range_ratio Scheme.Modules.ProjPresentation Scheme.Modules.ProjPresentation.mem_preimage_basicOpen_iff"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Hom.resLE_comp_ι Opens.toSpecΓ_SpecMap_presheaf_map_top_assoc toSpecΓ_naturality_assoc Hom Γ isoSpec_hom Opens.toSpecΓ_SpecMap_appLE_assoc basicOpen isBasis_affineOpens Modules Opens hom_ext_of_forall Hom.appLE_map Hom.app_eq_appLE Modules.map_smul ΓSpecIso toSpecΓ Modules.ProjPresentation Modules.ProjPresentation.mem_preimage_basicOpen_iff"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "presheaf Hom map_smul ProjPresentation ProjPresentation.mem_preimage_basicOpen_iff"
namespace PRESUNIQ
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

section Uniq

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} {M : X.Modules} {N : ℕ}

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R

lemma exists_mem_basicOpen_X (y : Proj 𝒜) : ∃ j : Fin (N + 1), y ∈ Proj.basicOpen 𝒜 (MvPolynomial.X j) := by
  have htop := Proj.iSup_basicOpen_eq_top 𝒜 (MvPolynomial.X : Fin (N + 1) → MvPolynomial (Fin (N + 1)) R)
    (ProjSpace.irrelevant_le_span_X R N)
  have hy : y ∈ (⊤ : (Proj 𝒜).Opens) := trivial
  rw [← htop] at hy
  exact Opens.mem_iSup.mp hy

theorem preimage_basicOpen_eq (𝔓 𝔔 : M.ProjPresentation f N) (h : ∀ i : Fin (N + 1), 𝔓.σ i = 𝔔.σ i) (i : Fin (N + 1)) :
    𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X i) = 𝔔.toProj ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X i) := by
  ext x
  constructor
  · intro hx
    have h1 := (AlgebraicGeometry.Scheme.Modules.ProjPresentation.mem_preimage_basicOpen_iff 𝔓 i x).1 hx
    rw [h i] at h1
    exact (AlgebraicGeometry.Scheme.Modules.ProjPresentation.mem_preimage_basicOpen_iff 𝔔 i x).2 h1
  · intro hx
    have h1 := (AlgebraicGeometry.Scheme.Modules.ProjPresentation.mem_preimage_basicOpen_iff 𝔔 i x).1 hx
    rw [← h i] at h1
    exact (AlgebraicGeometry.Scheme.Modules.ProjPresentation.mem_preimage_basicOpen_iff 𝔓 i x).2 h1

theorem chartRing_eq (𝔓 𝔔 : M.ProjPresentation f N) (h : ∀ i : Fin (N + 1), 𝔓.σ i = 𝔔.σ i) (i : Fin (N + 1))
    (V : X.Opens) (hV : IsAffineOpen V)
    (hP : V ≤ 𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X i))
    (hQ : V ≤ 𝔔.toProj ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X i)) :
    chartRing 𝔓.toProj i V hP = chartRing 𝔔.toProj i V hQ := by
  letI : Algebra R Γ(X, V) := (algR f V).toAlgebra
  let φP : Away 𝒜 (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) R) →ₐ[R] Γ(X, V) :=
    { toRingHom := chartRing 𝔓.toProj i V hP
      commutes' := fun r => chartRing_algebraMap f 𝔓.toProj i V hP hV 𝔓.toProj_π r }
  let φQ : Away 𝒜 (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) R) →ₐ[R] Γ(X, V) :=
    { toRingHom := chartRing 𝔔.toProj i V hQ
      commutes' := fun r => chartRing_algebraMap f 𝔔.toProj i V hQ hV 𝔔.toProj_π r }
  have hφ : φP = φQ := by
    refine AlgHom.ext_of_adjoin_eq_top (ProjSpace.adjoin_range_ratio R N i) ?_
    rintro _ ⟨l, rfl⟩
    show chartRing 𝔓.toProj i V hP (ProjSpace.ratio R N i l) = chartRing 𝔔.toProj i V hQ (ProjSpace.ratio R N i l)
    apply (isFrameOn 𝔓 i V hP).injective
    rw [chartRing_ratio_smul 𝔓 i V hP l, h i, h l, chartRing_ratio_smul 𝔔 i V hQ l]
  exact congrArg AlgHom.toRingHom hφ

end Uniq

end

end AlgebraicGeometry.Scheme.Modules.PRESUNIQ

open AlgebraicGeometry.Scheme.Modules.PRESUNIQ in
attribute [local instance] MvPolynomial.gradedAlgebra in
theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} {M : X.Modules} {N : ℕ}
    (𝔓 𝔔 : M.ProjPresentation f N) (h : ∀ i : Fin (N + 1), 𝔓.σ i = 𝔔.σ i) :
    𝔓.toProj = 𝔔.toProj := by
  apply Scheme.hom_ext_of_forall
  intro x
  obtain ⟨i, hi⟩ := exists_mem_basicOpen_X (R := R) (N := N) (𝔓.toProj x)
  have hxU : x ∈ 𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i) := hi
  obtain ⟨V, hV, hxV, hVU⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hxU
  refine ⟨V, hxV, ?_⟩
  have hV' : IsAffineOpen V := hV
  have hU := preimage_basicOpen_eq 𝔓 𝔔 h i
  have hVQ : V ≤ 𝔔.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i) :=
    hVU.trans hU.le
  rw [fac 𝔓.toProj i V hVU, fac 𝔔.toProj i V hVQ, chartRing_eq 𝔓 𝔔 h i V hV' hVU hVQ]

end S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_toProj_eq_of_forall_sections_eq_univ
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_toProj_eq_of_forall_sections_eq_univ (solution)
