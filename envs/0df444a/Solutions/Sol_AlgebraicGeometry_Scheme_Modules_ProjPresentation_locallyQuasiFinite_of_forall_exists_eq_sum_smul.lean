-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.ProjPresentation.locallyQuasiFinite_of_forall_exists_eq_sum_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/ce245bae-f175-5799-8afe-0b98b8a33739

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_algHom_away_apply_ratio_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_locallyQuasiFinite_of_forall_exists_eq_sum_smul

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace MvPolynomial HomogeneousLocalization AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_locallyQuasiFinite_of_forall_exists_eq_sum_smul.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.resLE_comp_ι Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top_assoc Spec.map_inj Scheme.toSpecΓ_naturality_assoc Scheme.Hom Proj.basicOpenIsoSpec Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc Proj.basicOpenIsoAway LocallyQuasiFinite Spec Spec.map Scheme Proj.awayι Proj HasRingHomProperty.appLE toSpecΓ_SpecMap_ΓSpecIso_inv Proj.isAffineOpen_basicOpen Proj.basicOpen Proj.basicOpenIsoAway_hom IsAffineOpen Scheme.Modules Scheme.Opens Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Proj.iSup_basicOpen_eq_top Proj.awayToSection HasRingHomProperty Proj.basicOpenIsoSpec_hom toSpecΓ HasRingHomProperty.iff_exists_appLE Scheme.ΓSpecIso ProjSpace.π ProjSpace.irrelevant_le_span_X ProjSpace.X_mem_one ProjSpace.awayι_comp_π ProjSpace.ratio ProjSpace.adjoin_range_ratio ProjSpace.exists_algHom_away_apply_ratio_eq"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Hom.resLE_comp_ι Opens.toSpecΓ_SpecMap_presheaf_map_top_assoc toSpecΓ_naturality_assoc Hom Γ isoSpec_hom Opens.toSpecΓ_SpecMap_appLE_assoc basicOpen isBasis_affineOpens Modules Opens Hom.appLE_map Hom.app_eq_appLE Modules.map_smul ΓSpecIso toSpecΓ"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "presheaf Hom map_smul ProjPresentation"
namespace SF
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

section Main

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} {M : X.Modules} {N N' : ℕ}
  (𝔓 : M.ProjPresentation f N) (𝔔 : M.ProjPresentation f N')

set_option maxHeartbeats 3200000 in

theorem quasiFinite_chartRing (i : Fin (N + 1)) (j : Fin (N' + 1)) (V : X.Opens) (hV : IsAffineOpen V)
    (hVi : V ≤ 𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i))
    (hVj : V ≤ 𝔔.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) R) (MvPolynomial.X j))
    (c : Fin (N + 1) → Fin (N' + 1) → R)
    (hc : ∀ l, resTop M (𝔓.σ l) V = ∑ k, algR f V (c l k) • resTop M (𝔔.σ k) V)
    (hα : (chartRing 𝔓.toProj i V hVi).QuasiFinite) :
    (chartRing 𝔔.toProj j V hVj).QuasiFinite := by
  classical
  set α := chartRing 𝔓.toProj i V hVi with hαdef
  set β := chartRing 𝔔.toProj j V hVj with hβdef
  have hFi : IsFrameOn M (𝔓.σ i) V := isFrameOn 𝔓 i V hVi
  have hFj : IsFrameOn M (𝔔.σ j) V := isFrameOn 𝔔 j V hVj

  let Ay := Away (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) R) (MvPolynomial.X j : MvPolynomial (Fin (N' + 1)) R)
  let a : Fin (N + 1) → Ay := fun l => ∑ k, algebraMap R Ay (c l k) * ProjSpace.ratio R N' j k
  have hβa : ∀ l, β (a l) • resTop M (𝔔.σ j) V = resTop M (𝔓.σ l) V := by
    intro l
    simp only [a, map_sum, map_mul, Finset.sum_smul, mul_smul]
    rw [hc l]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hβdef, chartRing_algebraMap f 𝔔.toProj j V hVj hV 𝔔.toProj_π, chartRing_ratio_smul 𝔔 j V hVj k]

  have hu : IsUnit (β (a i)) := hFj.isUnit_of_eq_smul hFi _ (hβa i).symm

  have hαr : ∀ l, α (ProjSpace.ratio R N i l) * β (a i) = β (a l) := by
    intro l
    apply hFj.injective
    show (α (ProjSpace.ratio R N i l) * β (a i)) • resTop M (𝔔.σ j) V = β (a l) • resTop M (𝔔.σ j) V
    rw [mul_smul, hβa i, hαdef, chartRing_ratio_smul 𝔓 i V hVi l, hβa l]

  let βt : Localization.Away (a i) →+* Γ(X, V) :=
    IsLocalization.Away.lift (S := Localization.Away (a i)) (a i) (g := β) hu
  have hβt : βt.comp (algebraMap Ay (Localization.Away (a i))) = β :=
    IsLocalization.Away.lift_comp (S := Localization.Away (a i)) (a i) hu
  have hβt' : ∀ y, βt (algebraMap Ay (Localization.Away (a i)) y) = β y := fun y =>
    IsLocalization.Away.lift_eq (S := Localization.Away (a i)) (a i) hu y
  have algRB_apply : ∀ r, algebraMap R (Localization.Away (a i)) r
      = algebraMap Ay (Localization.Away (a i)) (algebraMap R Ay r) := fun r =>
    IsScalarTower.algebraMap_apply R Ay (Localization.Away (a i)) r

  obtain ⟨γ, hγ⟩ := ProjSpace.exists_algHom_away_apply_ratio_eq R N i (B := Localization.Away (a i))
    (fun l => algebraMap Ay (Localization.Away (a i)) (a l) * IsLocalization.Away.invSelf (a i))
    (by exact IsLocalization.Away.mul_invSelf (a i))

  letI algRV : Algebra R Γ(X, V) := (β.comp (algebraMap R Ay)).toAlgebra
  have algRV_apply : ∀ r, algebraMap R Γ(X, V) r = β (algebraMap R Ay r) := fun r => rfl
  have hαβR : ∀ r, α (algebraMap R _ r) = β (algebraMap R Ay r) := fun r =>
    (chartRing_algebraMap f 𝔓.toProj i V hVi hV 𝔓.toProj_π r).trans
      (chartRing_algebraMap f 𝔔.toProj j V hVj hV 𝔔.toProj_π r).symm
  let αA : Away (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) R)
      →ₐ[R] Γ(X, V) :=
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
  have key : α = βt.comp γ.toRingHom := by
    have := congrArg AlgHom.toRingHom hAlg
    exact this

  have h1 : (βt.comp γ.toRingHom).QuasiFinite := key ▸ hα
  have h2 := RingHom.QuasiFinite.of_comp (f := βt) (g := γ.toRingHom) h1
  have h3 := RingHom.QuasiFinite.holdsForLocalizationAway (Localization.Away (a i)) (a i)
  rw [← hβt]
  exact RingHom.QuasiFinite.comp h2 h3

theorem quasiFinite_appLE_iff (t : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)) (i : Fin (N + 1))
    (V : X.Opens)
    (hle : V ≤ t ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)) :
    (t.appLE (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)) V hle).hom.QuasiFinite
      ↔ (chartRing t i V hle).QuasiFinite := by
  let e := (Proj.basicOpenIsoAway (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)
    (ProjSpace.X_mem_one R N i) one_pos).commRingCatIsoToRingEquiv
  have he : (chartRing t i V hle) =
      (t.appLE (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)) V hle).hom.comp
        e.toRingHom := by
    ext z
    show _ = (t.appLE _ V hle) ((Proj.basicOpenIsoAway _ (MvPolynomial.X i) (ProjSpace.X_mem_one R N i) one_pos).hom z)
    rw [Proj.basicOpenIsoAway_hom]
    rfl
  constructor
  · intro h
    rw [he]
    exact RingHom.QuasiFinite.respectsIso.2 _ e h
  · intro h
    have h' := RingHom.QuasiFinite.respectsIso.2 _ e.symm h
    rw [he] at h'
    convert h' using 1
    ext z
    simp

theorem hc_res (c : Fin (N + 1) → Fin (N' + 1) → R)
    (hc : ∀ l, 𝔓.σ l = ∑ k, (f.appTop ((Scheme.ΓSpecIso (.of R)).inv (c l k))) • 𝔔.σ k) (V : X.Opens) (l : Fin (N + 1)) :
    resTop M (𝔓.σ l) V = ∑ k, algR f V (c l k) • resTop M (𝔔.σ k) V := by
  have h := congrArg (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op) (hc l)
  rw [map_sum] at h
  refine h.trans (Finset.sum_congr rfl fun k _ => ?_)
  rw [Modules.map_smul]
  rfl

theorem locallyQuasiFinite [LocallyQuasiFinite 𝔓.toProj]
    (h : ∀ i : Fin (N + 1), ∃ c : Fin (N' + 1) → R,
      𝔓.σ i = ∑ j, (f.appTop ((Scheme.ΓSpecIso (.of R)).inv (c j))) • 𝔔.σ j) :
    LocallyQuasiFinite 𝔔.toProj := by
  classical
  choose c hc using h
  have hQ : RingHom.StableUnderCompositionWithLocalizationAwaySource @RingHom.QuasiFinite :=
    (RingHom.QuasiFinite.stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.QuasiFinite.holdsForLocalizationAway).1
  rw [HasRingHomProperty.iff_exists_appLE (P := @LocallyQuasiFinite) hQ]
  intro x

  have hcovP : (⨆ i : Fin (N + 1), Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
      (MvPolynomial.X i)) = ⊤ :=
    Proj.iSup_basicOpen_eq_top _ _ (ProjSpace.irrelevant_le_span_X R N)
  have hcovQ : (⨆ j : Fin (N' + 1), Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) R)
      (MvPolynomial.X j)) = ⊤ :=
    Proj.iSup_basicOpen_eq_top _ _ (ProjSpace.irrelevant_le_span_X R N')
  have hxP : 𝔓.toProj.base x ∈ (⨆ i : Fin (N + 1), Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
      (MvPolynomial.X i)) := by rw [hcovP]; trivial
  have hxQ : 𝔔.toProj.base x ∈ (⨆ j : Fin (N' + 1), Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) R)
      (MvPolynomial.X j)) := by rw [hcovQ]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hxP
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hxQ

  let W : X.Opens := (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
      (MvPolynomial.X i)) ⊓
    (𝔔.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) R) (MvPolynomial.X j))
  have hxW : x ∈ W := ⟨hi, hj⟩
  obtain ⟨_, ⟨V, hVaff, rfl⟩, hxV, hVW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hxW W.2
  have hVi : V ≤ 𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
      (MvPolynomial.X i) := fun p hp => (hVW hp).1
  have hVj : V ≤ 𝔔.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) R)
      (MvPolynomial.X j) := fun p hp => (hVW hp).2
  refine ⟨⟨_, Proj.isAffineOpen_basicOpen _ (MvPolynomial.X j) (ProjSpace.X_mem_one R N' j) one_pos⟩, ⟨V, hVaff⟩,
    hxV, hVj, ?_⟩

  have hα : (chartRing 𝔓.toProj i V hVi).QuasiFinite := by
    rw [← quasiFinite_appLE_iff]
    exact HasRingHomProperty.appLE @LocallyQuasiFinite 𝔓.toProj inferInstance
      ⟨_, Proj.isAffineOpen_basicOpen _ (MvPolynomial.X i) (ProjSpace.X_mem_one R N i) one_pos⟩ ⟨V, hVaff⟩ hVi
  show (𝔔.toProj.appLE _ V hVj).hom.QuasiFinite
  rw [quasiFinite_appLE_iff]
  exact quasiFinite_chartRing 𝔓 𝔔 i j V hVaff hVi hVj c (hc_res 𝔓 𝔔 c hc V) hα

end Main

end

end AlgebraicGeometry.Scheme.Modules.SF

open CategoryTheory _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_locallyQuasiFinite_of_forall_exists_eq_sum_smul.AlgebraicGeometry in
attribute [local instance] MvPolynomial.gradedAlgebra in
theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} {M : X.Modules} {N N' : ℕ}
    (𝔓 : M.ProjPresentation f N) (𝔔 : M.ProjPresentation f N') [LocallyQuasiFinite 𝔓.toProj]
    (h : ∀ i : Fin (N + 1), ∃ c : Fin (N' + 1) → R,
      𝔓.σ i = ∑ j, (f.appTop ((Scheme.ΓSpecIso (.of R)).inv (c j))) • 𝔔.σ j) :
    LocallyQuasiFinite 𝔔.toProj :=
  AlgebraicGeometry.Scheme.Modules.SF.locallyQuasiFinite 𝔓 𝔔 h

end S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_locallyQuasiFinite_of_forall_exists_eq_sum_smul
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_locallyQuasiFinite_of_forall_exists_eq_sum_smul (solution)
