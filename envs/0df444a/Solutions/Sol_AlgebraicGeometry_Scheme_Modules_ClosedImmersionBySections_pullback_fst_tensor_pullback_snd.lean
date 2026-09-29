-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.ClosedImmersionBySections.pullback_fst_tensor_pullback_snd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/0906ec11-d7ca-512e-8bb1-5be41fdbea70

import Mathlib
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_projPresentation_pullback_sigma_eq_toProj_eq
import Theorems.Thm_AlgebraicGeometry_isAffineOpen_pullback_fst_preimage_inf_snd_preimage_and_closure_eq_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_fst_tensor_pullback_snd

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Scheme.Hom.congr_app Scheme.Opens.topIso_inv Surjective HasAffineProperty HasAffineProperty.iff_of_iSup_eq_top Scheme.Modules.pullback Scheme.Hom morphismRestrict_appTop Proj.basicOpenIsoSpec Scheme.preimage_basicOpen Spec Spec.map Proj.basicOpenToSpec Scheme.ΓSpecIso_inv_naturality Scheme Scheme.mem_basicOpen'' Scheme.Hom.appTop Proj.mem_basicOpen Scheme.Hom.comp_appTop Proj Scheme.Hom.naturality IsClosedImmersion Proj.stalkIso' Proj.basicOpenIsoSpec_inv_ι Proj.isAffineOpen_basicOpen Proj.basicOpen Proj.basicOpenIsoAway_hom IsAffineOpen Scheme.Modules Scheme.Hom.preimage_iSup Scheme.Opens Proj.iSup_basicOpen_eq_top Scheme.Opens.ι_image_top Scheme.Opens.ι_appTop Proj.awayToSection Proj.basicOpenToSpec_app_top Proj.basicOpenIsoSpec_hom Scheme.Modules.map_smul ProjectiveSpectrum.Proj.awayToSection_germ Scheme.ΓSpecIso Scheme.Modules.ProjPresentation Scheme.Modules.ClosedImmersionBySections ProjSpace.π ProjSpace.irrelevant_le_span_X ProjSpace.X_mem_one ProjSpace.awayι_comp_π ProjSpace.ratio ProjSpace.ratio_self ProjSpace.adjoin_range_ratio Scheme.Modules.tensorSections Scheme.Modules.tensorSections_smul_left Scheme.Modules.tensorSections_smul_right Scheme.Modules.map_homOfLE_tensorSections Scheme.Modules.IsFrameOn Scheme.Modules.IsFrameOn.tensorSections_monoidalV2 Scheme.Modules.exists_projPresentation_of_iSup_eq_top Scheme.Modules.ProjPresentation.exists_projPresentation_pullback_sigma_eq_toProj_eq isAffineOpen_pullback_fst_preimage_inf_snd_preimage_and_closure_eq_top" namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Hom.congr_app mem_basicOpen basicOpen_res Opens.topIso_inv basicOpen_of_isUnit Modules.pullback Hom mk Γ topIso preimage_basicOpen ΓSpecIso_inv_naturality mem_basicOpen'' Hom.appTop Hom.comp_appTop Hom.naturality affineOpens basicOpen Modules Hom.preimage_iSup Opens Opens.ι_image_top Opens.ι_appTop Modules.map_smul ΓSpecIso Modules.ProjPresentation Modules.ClosedImmersionBySections Modules.tensorSections Modules.tensorSections_smul_left Modules.tensorSections_smul_right Modules.map_homOfLE_tensorSections Modules.IsFrameOn Modules.IsFrameOn.tensorSections_monoidalV2 Modules.exists_projPresentation_of_iSup_eq_top Modules.ProjPresentation.exists_projPresentation_pullback_sigma_eq_toProj_eq" namespace Modules p2m_export "AlgebraicGeometry.Scheme.Modules" "pullback presheaf Hom map_smul tensor ProjPresentation ClosedImmersionBySections tensorSections tensorSections_smul_left tensorSections_smul_right map_homOfLE_tensorSections IsFrameOn IsFrameOn.tensorSections_monoidalV2 exists_projPresentation_of_iSup_eq_top ProjPresentation.exists_projPresentation_pullback_sigma_eq_toProj_eq" namespace IsFrameOn p2m_export "AlgebraicGeometry.Scheme.Modules.IsFrameOn" "mono map tensorSections_monoidalV2" end AlgebraicGeometry.Scheme.Modules.IsFrameOn
namespace AlgebraicGeometry.Scheme.Modules.IsFrameOn
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.IsFrameOn" in
private alias _root_.AlgebraicGeometry.Scheme.Modules.IsFrameOn.tensorSections :=
  AlgebraicGeometry.Scheme.Modules.IsFrameOn.tensorSections_monoidalV2

end AlgebraicGeometry.Scheme.Modules.IsFrameOn
p2m_export "" "AlgebraicGeometry.Scheme.Modules.IsFrameOn.tensorSections"
set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_fst_tensor_pullback_snd.AlgebraicGeometry Opposite TopologicalSpace"

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

noncomputable section

namespace P2mSegreCI

section Frame

variable {X : Scheme.{u}} {M : X.Modules} {W : X.Opens}

theorem map_homOfLE_refl (s : Γ(M, W)) : M.presheaf.map (homOfLE (le_refl W)).op s = s := by
  have : (homOfLE (le_refl W)).op = 𝟙 (op W) := Subsingleton.elim _ _
  rw [this, CategoryTheory.Functor.map_id]
  rfl

theorem smul_left_injective_of_isFrameOn {s : Γ(M, W)} (hs : Scheme.Modules.IsFrameOn s W) :
    Function.Injective fun g : Γ(X, W) => g • s := by
  have h := (hs (le_refl W) (le_refl W)).1
  simpa only [map_homOfLE_refl] using h

theorem smul_left_surjective_of_isFrameOn {s : Γ(M, W)} (hs : Scheme.Modules.IsFrameOn s W) :
    Function.Surjective fun g : Γ(X, W) => g • s := by
  have h := (hs (le_refl W) (le_refl W)).2
  simpa only [map_homOfLE_refl] using h

theorem isUnit_of_smul_frame_eq_frame {s t : Γ(M, W)} (hs : Scheme.Modules.IsFrameOn s W)
    (ht : Scheme.Modules.IsFrameOn t W) {c : Γ(X, W)} (hc : c • s = t) : IsUnit c := by
  obtain ⟨d, hd⟩ := smul_left_surjective_of_isFrameOn ht s
  change d • t = s at hd
  have h1 : (d * c) • s = (1 : Γ(X, W)) • s := by rw [mul_smul, hc, hd, one_smul]
  have h2 : d * c = 1 := smul_left_injective_of_isFrameOn hs h1
  exact isUnit_iff_exists_inv'.mpr ⟨d, h2⟩

theorem isFrameOn_map {U V : X.Opens} {s : Γ(M, U)} (hs : Scheme.Modules.IsFrameOn s V)
    (hWU : W ≤ U) (hWV : W ≤ V) :
    Scheme.Modules.IsFrameOn (M.presheaf.map (homOfLE hWU).op s) W :=
  (hs.map (homOfLE hWU)).mono hWV

end Frame

section OnePresentation

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)}
  {M : X.Modules} {N : ℕ} (𝔓 : M.ProjPresentation f N)

abbrev PP (R : Type u) [CommRing R] (N : ℕ) : Scheme.{u} :=
  Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)

abbrev DD (R : Type u) [CommRing R] (N : ℕ) (i : Fin (N + 1)) : (PP R N).Opens :=
  Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)

abbrev chart (i : Fin (N + 1)) : X.Opens := 𝔓.toProj ⁻¹ᵁ DD R N i

theorem iSup_DD : ⨆ i, DD R N i = ⊤ :=
  Proj.iSup_basicOpen_eq_top _ (fun i => MvPolynomial.X i) (ProjSpace.irrelevant_le_span_X R N)

theorem iSup_chart : ⨆ i, chart 𝔓 i = ⊤ := by
  rw [← Scheme.Hom.preimage_iSup, iSup_DD]
  rfl

theorem exists_mem_chart (x : X) : ∃ i, x ∈ chart 𝔓 i := by
  have hx : x ∈ (⨆ i, chart 𝔓 i) := by rw [iSup_chart]; trivial
  exact Opens.mem_iSup.mp hx

theorem isFrameOn_σ (i : Fin (N + 1)) : Scheme.Modules.IsFrameOn (𝔓.σ i) (chart 𝔓 i) :=
  fun _ _ hWV => 𝔓.frame i _ hWV

noncomputable def rfun (i j : Fin (N + 1)) : Γ(X, chart 𝔓 i) :=
  𝔓.toProj.app (DD R N i) (Proj.awayToSection _ (MvPolynomial.X i) (ProjSpace.ratio R N i j))

theorem rfun_smul (i j : Fin (N + 1)) :
    rfun 𝔓 i j • M.presheaf.map (homOfLE (le_top : chart 𝔓 i ≤ ⊤)).op (𝔓.σ i) =
      M.presheaf.map (homOfLE (le_top : chart 𝔓 i ≤ ⊤)).op (𝔓.σ j) :=
  𝔓.app_ratio_smul i j

end OnePresentation

section Maps

variable {X : Scheme.{u}}

theorem pmap_congr {U V : X.Opens} (i j : op U ⟶ op V) (s : Γ(X, U)) :
    X.presheaf.map i s = X.presheaf.map j s := by
  rw [Subsingleton.elim i j]

theorem pmap_pmap {U V W : X.Opens} (i : op U ⟶ op V) (j : op V ⟶ op W) (s : Γ(X, U)) :
    X.presheaf.map j (X.presheaf.map i s) = X.presheaf.map (i ≫ j) s := by
  rw [CategoryTheory.Functor.map_comp]
  rfl

theorem pmap_self {U : X.Opens} (i : op U ⟶ op U) (s : Γ(X, U)) : X.presheaf.map i s = s := by
  rw [Subsingleton.elim i (𝟙 _), CategoryTheory.Functor.map_id]
  rfl

theorem surjective_comp_eqToHom {A : CommRingCat.{u}} {U V : X.Opens} (h : U = V)
    (a : A ⟶ X.presheaf.obj (op V)) (ha : Function.Surjective a) :
    Function.Surjective (a ≫ X.presheaf.map (eqToHom h).op) := by
  cases h
  rw [eqToHom_refl, op_id, CategoryTheory.Functor.map_id, Category.comp_id]
  exact ha

end Maps

section Scalars

variable (R : Type u) [CommRing R] (N : ℕ)

theorem awayToSection_algebraMap (i : Fin (N + 1)) (r : R) :
    Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)
        (algebraMap R (HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
          (MvPolynomial.X i)) r) =
      (PP R N).presheaf.map (homOfLE (le_top : DD R N i ≤ ⊤)).op
        ((ProjSpace.π R N).appTop ((Scheme.ΓSpecIso (.of R)).inv r)) := by
  set 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R with h𝒜
  set A := HomogeneousLocalization.Away 𝒜 (MvPolynomial.X i) with hA

  have h1 : (DD R N i).ι ≫ ProjSpace.π R N =
      (Proj.basicOpenIsoSpec 𝒜 (MvPolynomial.X i) (ProjSpace.X_mem_one R N i) one_pos).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
    rw [← Iso.inv_comp_eq, ← Category.assoc, Proj.basicOpenIsoSpec_inv_ι]
    exact ProjSpace.awayι_comp_π R N i
  have h2 := congrArg (fun φ => Scheme.Hom.appTop φ ((Scheme.ΓSpecIso (.of R)).inv r)) h1
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at h2

  have h3 : (Spec.map (CommRingCat.ofHom (algebraMap R A))).appTop ((Scheme.ΓSpecIso (.of R)).inv r) =
      (Scheme.ΓSpecIso (.of A)).inv (algebraMap R A r) := by
    have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R A))
    exact (ConcreteCategory.congr_hom this r).symm
  rw [h3, Proj.basicOpenIsoSpec_hom] at h2
  have h4 : (Proj.basicOpenToSpec 𝒜 (MvPolynomial.X i)).appTop ((Scheme.ΓSpecIso (.of A)).inv (algebraMap R A r)) =
      (DD R N i).topIso.inv (Proj.awayToSection 𝒜 (MvPolynomial.X i) (algebraMap R A r)) := by
    change (Proj.basicOpenToSpec 𝒜 (MvPolynomial.X i)).app ⊤ _ = _
    rw [Proj.basicOpenToSpec_app_top]
    change (DD R N i).topIso.inv (Proj.awayToSection 𝒜 (MvPolynomial.X i)
      ((Scheme.ΓSpecIso (.of A)).hom ((Scheme.ΓSpecIso (.of A)).inv (algebraMap R A r)))) = _
    rw [Iso.inv_hom_id_apply]
  rw [h4, Scheme.Opens.topIso_inv, Scheme.Opens.ι_appTop] at h2

  have h2' : ((PP R N).presheaf.map (homOfLE (le_top : (DD R N i).ι ''ᵁ ⊤ ≤ ⊤)).op)
        ((ProjSpace.π R N).appTop ((Scheme.ΓSpecIso (.of R)).inv r)) =
      ((PP R N).presheaf.map (eqToHom (DD R N i).ι_image_top).op)
        (Proj.awayToSection 𝒜 (MvPolynomial.X i) (algebraMap R A r)) := h2
  have h5 := congrArg ((PP R N).presheaf.map (eqToHom (DD R N i).ι_image_top.symm).op) h2'
  rw [pmap_pmap, pmap_pmap, pmap_self] at h5
  rw [← h5]
  exact pmap_congr _ _ _

variable {R N}

theorem app_awayToSection_algebraMap {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} (φ : X ⟶ PP R N)
    (hφ : φ ≫ ProjSpace.π R N = f) (i : Fin (N + 1)) (r : R) :
    φ.app (DD R N i) (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)
        (algebraMap R (HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
          (MvPolynomial.X i)) r)) =
      X.presheaf.map (homOfLE (le_top : φ ⁻¹ᵁ DD R N i ≤ ⊤)).op (f.appTop ((Scheme.ΓSpecIso (.of R)).inv r)) := by
  rw [awayToSection_algebraMap]
  have nat := Scheme.Hom.naturality φ (homOfLE (le_top : DD R N i ≤ ⊤)).op
  have h := ConcreteCategory.congr_hom nat ((ProjSpace.π R N).appTop ((Scheme.ΓSpecIso (.of R)).inv r))
  change φ.app (DD R N i) ((PP R N).presheaf.map (homOfLE (le_top : DD R N i ≤ ⊤)).op
      ((ProjSpace.π R N).appTop ((Scheme.ΓSpecIso (.of R)).inv r))) =
    X.presheaf.map ((Opens.map φ.base).map (homOfLE (le_top : DD R N i ≤ ⊤)).op.unop).op
      (φ.appTop ((ProjSpace.π R N).appTop ((Scheme.ΓSpecIso (.of R)).inv r))) at h
  rw [h, ← hφ, Scheme.Hom.comp_appTop]
  exact pmap_congr _ _ _

end Scalars

section Generation

variable (R : Type u) [CommRing R] (N : ℕ)

theorem mem_closure_awayToSection (i : Fin (N + 1)) (x : Γ(PP R N, DD R N i)) :
    x ∈ Subring.closure
      (Set.range (fun r : R => Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
          (MvPolynomial.X i) (algebraMap R _ r)) ∪
        Set.range (fun a : Fin (N + 1) => Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
          (MvPolynomial.X i) (ProjSpace.ratio R N i a))) := by
  set 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R with h𝒜
  haveI : IsIso (Proj.awayToSection 𝒜 (MvPolynomial.X i)) := by
    rw [← Proj.basicOpenIsoAway_hom 𝒜 (MvPolynomial.X i) (ProjSpace.X_mem_one R N i) one_pos]
    infer_instance
  obtain ⟨z, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Proj.awayToSection 𝒜 (MvPolynomial.X i))).2 x
  have hz : z ∈ (Algebra.adjoin R (Set.range (ProjSpace.ratio R N i))).toSubring := by
    rw [ProjSpace.adjoin_range_ratio]; trivial
  rw [Algebra.adjoin_eq_ring_closure] at hz
  have hz' : (Proj.awayToSection 𝒜 (MvPolynomial.X i)).hom z ∈
      (Subring.closure (Set.range (algebraMap R _) ∪ Set.range (ProjSpace.ratio R N i))).map
        (Proj.awayToSection 𝒜 (MvPolynomial.X i)).hom :=
    Subring.mem_map.mpr ⟨z, hz, rfl⟩
  rw [RingHom.map_closure] at hz'
  refine Subring.closure_mono ?_ hz'
  rintro _ ⟨w, hw, rfl⟩
  rcases hw with ⟨r, rfl⟩ | ⟨a, rfl⟩
  · exact Or.inl ⟨r, rfl⟩
  · exact Or.inr ⟨a, rfl⟩

end Generation

section ProjRatio

variable (R : Type u) [CommRing R] (N : ℕ)

theorem mem_DD_of_isUnit_germ (i j : Fin (N + 1)) (p : PP R N) (hp : p ∈ DD R N i)
    (hu : IsUnit ((PP R N).presheaf.germ (DD R N i) p hp
      (Proj.awayToSection _ (MvPolynomial.X i) (ProjSpace.ratio R N i j)))) :
    p ∈ DD R N j := by
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R
  have hle : Submonoid.powers (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) R) ≤
      p.asHomogeneousIdeal.toIdeal.primeCompl := Submonoid.powers_le.mpr hp

  have hgerm := ProjectiveSpectrum.Proj.awayToSection_germ 𝒜 (MvPolynomial.X i) p hp
  have hcomp : (PP R N).presheaf.germ (DD R N i) p hp
      (Proj.awayToSection 𝒜 (MvPolynomial.X i) (ProjSpace.ratio R N i j)) =
      (Proj.stalkIso' 𝒜 p).toCommRingCatIso.inv
        (HomogeneousLocalization.mapId 𝒜 hle (ProjSpace.ratio R N i j)) := by
    have := congrArg (fun φ => (φ : _ → _) (ProjSpace.ratio R N i j)) (congrArg (fun φ => φ.hom) hgerm)
    first
      | simpa using this
      | (have h' := this; simp at h' ⊢; exact h')
      | (have h' := this; simp at h'; exact h')
      | exact this
  rw [hcomp] at hu

  have hu' : IsUnit (HomogeneousLocalization.mapId 𝒜 hle (ProjSpace.ratio R N i j)) :=
    (isUnit_map_iff (Proj.stalkIso' 𝒜 p).symm _).mp hu

  rw [← HomogeneousLocalization.isUnit_iff_isUnit_val] at hu'
  have hval : (HomogeneousLocalization.mapId 𝒜 hle (ProjSpace.ratio R N i j)).val =
      Localization.mk (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) R)
        ⟨MvPolynomial.X i ^ 1, hle ⟨1, rfl⟩⟩ := by
    rw [ProjSpace.ratio, HomogeneousLocalization.Away.mk, HomogeneousLocalization.mapId,
      HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk]
    rfl
  rw [hval, Localization.mk_eq_mk', IsLocalization.AtPrime.isUnit_mk'_iff] at hu'

  rw [Proj.mem_basicOpen]
  intro hmem
  exact hu' hmem

end ProjRatio

section OnePresentation2

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)}
  {M : X.Modules} {N : ℕ} (𝔓 : M.ProjPresentation f N)

theorem mem_chart_of_isUnit_rfun {i j : Fin (N + 1)} {O : X.Opens} (hO : O ≤ chart 𝔓 i) {x : X}
    (hx : x ∈ O) (hu : IsUnit (X.presheaf.map (homOfLE hO).op (rfun 𝔓 i j))) : x ∈ chart 𝔓 j := by
  have h1 : X.basicOpen (X.presheaf.map (homOfLE hO).op (rfun 𝔓 i j)) = O := X.basicOpen_of_isUnit hu
  have h2 : X.basicOpen (X.presheaf.map (homOfLE hO).op (rfun 𝔓 i j)) = O ⊓ X.basicOpen (rfun 𝔓 i j) :=
    X.basicOpen_res _ _
  have hx' : x ∈ X.basicOpen (rfun 𝔓 i j) := by
    have : x ∈ O ⊓ X.basicOpen (rfun 𝔓 i j) := by rw [← h2, h1]; exact hx
    exact this.2
  rw [rfun, ← Scheme.preimage_basicOpen] at hx'
  change 𝔓.toProj.base x ∈ (PP R N).basicOpen _ at hx'
  obtain ⟨hp, hunit⟩ := (Scheme.mem_basicOpen'' _ _ _).mp hx'
  exact mem_DD_of_isUnit_germ R N i j (𝔓.toProj.base x) hp hunit

end OnePresentation2

section Restrict

variable {X : Scheme.{u}} {M : X.Modules} {U V W : X.Opens}

theorem modMap_map (h₁ : V ≤ U) (h₂ : W ≤ V) (s : Γ(M, U)) :
    M.presheaf.map (homOfLE h₂).op (M.presheaf.map (homOfLE h₁).op s) =
      M.presheaf.map (homOfLE (h₂.trans h₁)).op s := by
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
  rfl

theorem ringMap_map (h₁ : V ≤ U) (h₂ : W ≤ V) (g : Γ(X, U)) :
    X.presheaf.map (homOfLE h₂).op (X.presheaf.map (homOfLE h₁).op g) =
      X.presheaf.map (homOfLE (h₂.trans h₁)).op g := by
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
  rfl

theorem restrict_smul_eq (h₁ : V ≤ U) (h₂ : W ≤ V) {g : Γ(X, V)} {s t : Γ(M, U)}
    (h : g • M.presheaf.map (homOfLE h₁).op s = M.presheaf.map (homOfLE h₁).op t) :
    X.presheaf.map (homOfLE h₂).op g • M.presheaf.map (homOfLE (h₂.trans h₁)).op s =
      M.presheaf.map (homOfLE (h₂.trans h₁)).op t := by
  have := congrArg (M.presheaf.map (homOfLE h₂).op) h
  rw [Scheme.Modules.map_smul, modMap_map, modMap_map] at this
  exact this

end Restrict

section Two

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)}
  {L M : X.Modules} {N N' : ℕ} (𝔓 : L.ProjPresentation f N) (𝔔 : M.ProjPresentation f N')

abbrev KK (N N' : ℕ) : ℕ := N * N' + N + N'

theorem KK_succ (N N' : ℕ) : (N + 1) * (N' + 1) = KK N N' + 1 := by
  simp only [KK]; ring

def idx (N N' : ℕ) : Fin (KK N N' + 1) ≃ Fin (N + 1) × Fin (N' + 1) :=
  (finCongr (KK_succ N N').symm).trans finProdFinEquiv.symm

def ρ (k : Fin (KK N N' + 1)) : Γ(L ⊗ M, ⊤) :=
  Scheme.Modules.tensorSections (𝔓.σ (idx N N' k).1) (𝔔.σ (idx N N' k).2)

abbrev WW (k : Fin (KK N N' + 1)) : X.Opens := chart 𝔓 (idx N N' k).1 ⊓ chart 𝔔 (idx N N' k).2

theorem iSup_WW : ⨆ k, WW 𝔓 𝔔 k = ⊤ := by
  refine top_le_iff.mp fun x _ => Opens.mem_iSup.mpr ?_
  obtain ⟨i, hi⟩ := exists_mem_chart 𝔓 x
  obtain ⟨j, hj⟩ := exists_mem_chart 𝔔 x
  refine ⟨(idx N N').symm (i, j), ?_⟩
  change x ∈ chart 𝔓 (idx N N' ((idx N N').symm (i, j))).1 ⊓ chart 𝔔 (idx N N' ((idx N N').symm (i, j))).2
  rw [Equiv.apply_symm_apply]
  exact ⟨hi, hj⟩

theorem exists_mem_WW (x : X) : ∃ k, x ∈ WW 𝔓 𝔔 k := by
  have hx : x ∈ (⨆ k, WW 𝔓 𝔔 k) := by rw [iSup_WW]; trivial
  exact Opens.mem_iSup.mp hx

theorem isFrameOn_ρ (k : Fin (KK N N' + 1)) : Scheme.Modules.IsFrameOn (ρ 𝔓 𝔔 k) (WW 𝔓 𝔔 k) :=
  Scheme.Modules.IsFrameOn.tensorSections ((isFrameOn_σ 𝔓 _).mono inf_le_left)
    ((isFrameOn_σ 𝔔 _).mono inf_le_right)

theorem exists_segre :
    ∃ 𝔖 : (L ⊗ M).ProjPresentation f (KK N N'), 𝔖.σ = ρ 𝔓 𝔔 ∧ ∀ k, WW 𝔓 𝔔 k ≤ chart 𝔖 k :=
  Scheme.Modules.exists_projPresentation_of_iSup_eq_top f (L ⊗ M) (KK N N') (ρ 𝔓 𝔔) (WW 𝔓 𝔔)
    (iSup_WW 𝔓 𝔔) (fun k _ hV => isFrameOn_ρ 𝔓 𝔔 k le_top hV)

theorem map_ρ (k : Fin (KK N N' + 1)) (O : X.Opens) :
    (L ⊗ M).presheaf.map (homOfLE (le_top : O ≤ ⊤)).op (ρ 𝔓 𝔔 k) =
      Scheme.Modules.tensorSections (L.presheaf.map (homOfLE (le_top : O ≤ ⊤)).op (𝔓.σ (idx N N' k).1))
        (M.presheaf.map (homOfLE (le_top : O ≤ ⊤)).op (𝔔.σ (idx N N' k).2)) :=
  Scheme.Modules.map_homOfLE_tensorSections _ _ _

variable {𝔓 𝔔}

theorem chart_segre_le (𝔖 : (L ⊗ M).ProjPresentation f (KK N N')) (hσ : 𝔖.σ = ρ 𝔓 𝔔)
    (hW : ∀ k, WW 𝔓 𝔔 k ≤ chart 𝔖 k) (k : Fin (KK N N' + 1)) : chart 𝔖 k ≤ WW 𝔓 𝔔 k := by
  intro x hx
  obtain ⟨k', hk'⟩ := exists_mem_WW 𝔓 𝔔 x

  set i := (idx N N' k).1 with hi
  set j := (idx N N' k).2 with hj
  set i' := (idx N N' k').1 with hi'
  set j' := (idx N N' k').2 with hj'

  let O : X.Opens := chart 𝔖 k ⊓ WW 𝔓 𝔔 k'
  have hxO : x ∈ O := ⟨hx, hk'⟩
  have hO_k : O ≤ chart 𝔖 k := inf_le_left
  have hO_k' : O ≤ chart 𝔖 k' := inf_le_right.trans (hW k')
  have hO_i' : O ≤ chart 𝔓 i' := inf_le_right.trans inf_le_left
  have hO_j' : O ≤ chart 𝔔 j' := inf_le_right.trans inf_le_right

  have fk : Scheme.Modules.IsFrameOn ((L ⊗ M).presheaf.map (homOfLE (le_top : O ≤ ⊤)).op (ρ 𝔓 𝔔 k)) O := by
    have h := isFrameOn_σ 𝔖 k
    rw [hσ] at h
    exact isFrameOn_map h le_top hO_k
  have fk' : Scheme.Modules.IsFrameOn ((L ⊗ M).presheaf.map (homOfLE (le_top : O ≤ ⊤)).op (ρ 𝔓 𝔔 k')) O := by
    have h := isFrameOn_σ 𝔖 k'
    rw [hσ] at h
    exact isFrameOn_map h le_top hO_k'

  have hc : X.presheaf.map (homOfLE hO_k').op (rfun 𝔖 k' k) •
      (L ⊗ M).presheaf.map (homOfLE (le_top : O ≤ ⊤)).op (ρ 𝔓 𝔔 k') =
      (L ⊗ M).presheaf.map (homOfLE (le_top : O ≤ ⊤)).op (ρ 𝔓 𝔔 k) := by
    have h := rfun_smul 𝔖 k' k
    rw [hσ] at h
    exact restrict_smul_eq le_top hO_k' h
  have hunit : IsUnit (X.presheaf.map (homOfLE hO_k').op (rfun 𝔖 k' k)) :=
    isUnit_of_smul_frame_eq_frame fk' fk hc

  have ha : X.presheaf.map (homOfLE hO_i').op (rfun 𝔓 i' i) •
      L.presheaf.map (homOfLE (le_top : O ≤ ⊤)).op (𝔓.σ i') =
      L.presheaf.map (homOfLE (le_top : O ≤ ⊤)).op (𝔓.σ i) :=
    restrict_smul_eq le_top hO_i' (rfun_smul 𝔓 i' i)
  have hb : X.presheaf.map (homOfLE hO_j').op (rfun 𝔔 j' j) •
      M.presheaf.map (homOfLE (le_top : O ≤ ⊤)).op (𝔔.σ j') =
      M.presheaf.map (homOfLE (le_top : O ≤ ⊤)).op (𝔔.σ j) :=
    restrict_smul_eq le_top hO_j' (rfun_smul 𝔔 j' j)
  have hab : (X.presheaf.map (homOfLE hO_i').op (rfun 𝔓 i' i) * X.presheaf.map (homOfLE hO_j').op (rfun 𝔔 j' j)) •
      (L ⊗ M).presheaf.map (homOfLE (le_top : O ≤ ⊤)).op (ρ 𝔓 𝔔 k') =
      (L ⊗ M).presheaf.map (homOfLE (le_top : O ≤ ⊤)).op (ρ 𝔓 𝔔 k) := by
    rw [map_ρ, map_ρ, ← hi, ← hj, ← hi', ← hj', ← ha, ← hb, Scheme.Modules.tensorSections_smul_left,
      Scheme.Modules.tensorSections_smul_right, ← mul_smul, mul_comm]

  have hcab : X.presheaf.map (homOfLE hO_k').op (rfun 𝔖 k' k) =
      X.presheaf.map (homOfLE hO_i').op (rfun 𝔓 i' i) * X.presheaf.map (homOfLE hO_j').op (rfun 𝔔 j' j) :=
    smul_left_injective_of_isFrameOn fk' (hc.trans hab.symm)
  rw [hcab] at hunit
  exact ⟨mem_chart_of_isUnit_rfun 𝔓 hO_i' hxO (isUnit_of_mul_isUnit_left hunit),
    mem_chart_of_isUnit_rfun 𝔔 hO_j' hxO (isUnit_of_mul_isUnit_right hunit)⟩

theorem rfun_segre_eq (𝔖 : (L ⊗ M).ProjPresentation f (KK N N')) (hσ : 𝔖.σ = ρ 𝔓 𝔔)
    (k l : Fin (KK N N' + 1)) {O : X.Opens} (hOk : O ≤ chart 𝔖 k)
    (hOi : O ≤ chart 𝔓 (idx N N' k).1) (hOj : O ≤ chart 𝔔 (idx N N' k).2) :
    X.presheaf.map (homOfLE hOk).op (rfun 𝔖 k l) =
      X.presheaf.map (homOfLE hOi).op (rfun 𝔓 (idx N N' k).1 (idx N N' l).1) *
        X.presheaf.map (homOfLE hOj).op (rfun 𝔔 (idx N N' k).2 (idx N N' l).2) := by
  have fk : Scheme.Modules.IsFrameOn ((L ⊗ M).presheaf.map (homOfLE (le_top : O ≤ ⊤)).op (ρ 𝔓 𝔔 k)) O := by
    have h := isFrameOn_σ 𝔖 k
    rw [hσ] at h
    exact isFrameOn_map h le_top hOk
  have hc : X.presheaf.map (homOfLE hOk).op (rfun 𝔖 k l) •
      (L ⊗ M).presheaf.map (homOfLE (le_top : O ≤ ⊤)).op (ρ 𝔓 𝔔 k) =
      (L ⊗ M).presheaf.map (homOfLE (le_top : O ≤ ⊤)).op (ρ 𝔓 𝔔 l) := by
    have h := rfun_smul 𝔖 k l
    rw [hσ] at h
    exact restrict_smul_eq le_top hOk h
  have ha : X.presheaf.map (homOfLE hOi).op (rfun 𝔓 (idx N N' k).1 (idx N N' l).1) •
      L.presheaf.map (homOfLE (le_top : O ≤ ⊤)).op (𝔓.σ (idx N N' k).1) =
      L.presheaf.map (homOfLE (le_top : O ≤ ⊤)).op (𝔓.σ (idx N N' l).1) :=
    restrict_smul_eq le_top hOi (rfun_smul 𝔓 _ _)
  have hb : X.presheaf.map (homOfLE hOj).op (rfun 𝔔 (idx N N' k).2 (idx N N' l).2) •
      M.presheaf.map (homOfLE (le_top : O ≤ ⊤)).op (𝔔.σ (idx N N' k).2) =
      M.presheaf.map (homOfLE (le_top : O ≤ ⊤)).op (𝔔.σ (idx N N' l).2) :=
    restrict_smul_eq le_top hOj (rfun_smul 𝔔 _ _)
  have hab : (X.presheaf.map (homOfLE hOi).op (rfun 𝔓 (idx N N' k).1 (idx N N' l).1) *
        X.presheaf.map (homOfLE hOj).op (rfun 𝔔 (idx N N' k).2 (idx N N' l).2)) •
      (L ⊗ M).presheaf.map (homOfLE (le_top : O ≤ ⊤)).op (ρ 𝔓 𝔔 k) =
      (L ⊗ M).presheaf.map (homOfLE (le_top : O ≤ ⊤)).op (ρ 𝔓 𝔔 l) := by
    rw [map_ρ, map_ρ, ← ha, ← hb, Scheme.Modules.tensorSections_smul_left,
      Scheme.Modules.tensorSections_smul_right, ← mul_smul, mul_comm]
  exact smul_left_injective_of_isFrameOn fk (hc.trans hab.symm)

end Two

section Transport

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {M : X.Modules} {N : ℕ}

def copyOver {f f' : X ⟶ Spec (.of R)} (h : f = f') (𝔓 : M.ProjPresentation f N) : M.ProjPresentation f' N where
  σ := 𝔓.σ
  toProj := 𝔓.toProj
  toProj_π := 𝔓.toProj_π.trans h
  frame := 𝔓.frame
  app_ratio_smul := 𝔓.app_ratio_smul

end Transport

theorem isAffineOpen_DD (R : Type u) [CommRing R] (N : ℕ) (i : Fin (N + 1)) : IsAffineOpen (DD R N i) :=
  Proj.isAffineOpen_basicOpen _ (MvPolynomial.X i) (ProjSpace.X_mem_one R N i) one_pos

section Product

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}
  {f : X ⟶ Spec (.of R)} {g : Y ⟶ Spec (.of R)}
  {L : X.Modules} {M : Y.Modules} {N N' : ℕ}
  (𝔓 : L.ProjPresentation f N) (𝔔 : M.ProjPresentation g N')

set_option maxHeartbeats 3200000 in

theorem closedImmersionBySections (hφ : IsClosedImmersion 𝔓.toProj) (hψ : IsClosedImmersion 𝔔.toProj) :
    Scheme.Modules.ClosedImmersionBySections
      ((Scheme.Modules.pullback (pullback.fst f g)).obj L ⊗ (Scheme.Modules.pullback (pullback.snd f g)).obj M)
      (pullback.fst f g ≫ f) := by
  haveI := hφ
  haveI := hψ
  obtain ⟨𝔓', -, hto'⟩ :=
    Scheme.Modules.ProjPresentation.exists_projPresentation_pullback_sigma_eq_toProj_eq (pullback.fst f g) 𝔓
  obtain ⟨𝔔₀, -, hto₀⟩ :=
    Scheme.Modules.ProjPresentation.exists_projPresentation_pullback_sigma_eq_toProj_eq (pullback.snd f g) 𝔔
  let 𝔔' : ((Scheme.Modules.pullback (pullback.snd f g)).obj M).ProjPresentation (pullback.fst f g ≫ f) N' :=
    copyOver pullback.condition.symm 𝔔₀
  obtain ⟨𝔖, hσ, hW⟩ := exists_segre 𝔓' 𝔔'
  refine ⟨KK N N', 𝔖, ?_⟩

  have hcP : ∀ i, chart 𝔓' i = pullback.fst f g ⁻¹ᵁ chart 𝔓 i := fun i => by
    change 𝔓'.toProj ⁻¹ᵁ _ = _
    rw [hto']
    rfl
  have hcQ : ∀ j, chart 𝔔' j = pullback.snd f g ⁻¹ᵁ chart 𝔔 j := fun j => by
    change 𝔔₀.toProj ⁻¹ᵁ _ = _
    rw [hto₀]
    rfl
  have hchart : ∀ k, chart 𝔖 k =
      pullback.fst f g ⁻¹ᵁ chart 𝔓 (idx N N' k).1 ⊓ pullback.snd f g ⁻¹ᵁ chart 𝔔 (idx N N' k).2 := fun k => by
    rw [← hcP, ← hcQ]
    exact le_antisymm (chart_segre_le 𝔖 hσ hW k) (hW k)
  have hU : ∀ i, IsAffineOpen (chart 𝔓 i) := fun i => (isAffineOpen_DD R N i).preimage 𝔓.toProj
  have hV : ∀ j, IsAffineOpen (chart 𝔔 j) := fun j => (isAffineOpen_DD R N' j).preimage 𝔔.toProj
  rw [HasAffineProperty.iff_of_iSup_eq_top (P := @IsClosedImmersion)
    (fun k => (⟨DD R (KK N N') k, isAffineOpen_DD R (KK N N') k⟩ : (PP R (KK N N')).affineOpens))
    (iSup_DD (R := R) (N := KK N N'))]
  intro k
  obtain ⟨haff, hgen⟩ :=
    AlgebraicGeometry.isAffineOpen_pullback_fst_preimage_inf_snd_preimage_and_closure_eq_top
      f g (hU (idx N N' k).1) (hV (idx N N' k).2)

  have hO₁ : chart 𝔖 k ≤ pullback.fst f g ⁻¹ᵁ chart 𝔓 (idx N N' k).1 := (hchart k).le.trans inf_le_left
  have hO₂ : chart 𝔖 k ≤ pullback.snd f g ⁻¹ᵁ chart 𝔔 (idx N N' k).2 := (hchart k).le.trans inf_le_right
  have hO₁' : chart 𝔖 k ≤ chart 𝔓' (idx N N' k).1 := by rw [hcP]; exact hO₁
  have hO₂' : chart 𝔖 k ≤ chart 𝔔' (idx N N' k).2 := by rw [hcQ]; exact hO₂

  have key : ∀ (O : (pullback f g).Opens) (h₁ : O ≤ pullback.fst f g ⁻¹ᵁ chart 𝔓 (idx N N' k).1)
      (h₂ : O ≤ pullback.snd f g ⁻¹ᵁ chart 𝔔 (idx N N' k).2),
      O = pullback.fst f g ⁻¹ᵁ chart 𝔓 (idx N N' k).1 ⊓ pullback.snd f g ⁻¹ᵁ chart 𝔔 (idx N N' k).2 →
      Subring.closure
        (Set.range (fun s : Γ(X, chart 𝔓 (idx N N' k).1) =>
            (pullback f g).presheaf.map (homOfLE h₁).op ((pullback.fst f g).app (chart 𝔓 (idx N N' k).1) s)) ∪
          Set.range (fun t : Γ(Y, chart 𝔔 (idx N N' k).2) =>
            (pullback f g).presheaf.map (homOfLE h₂).op ((pullback.snd f g).app (chart 𝔔 (idx N N' k).2) t))) = ⊤ := by
    rintro O h₁ h₂ rfl
    exact hgen
  have hgenO := key (chart 𝔖 k) hO₁ hO₂ (hchart k)

  have core : Function.Surjective (𝔖.toProj.app (DD R (KK N N') k)) := by
    let Im : Subring Γ(pullback f g, chart 𝔖 k) := (𝔖.toProj.app (DD R (KK N N') k)).hom.range
    suffices htop : (⊤ : Subring Γ(pullback f g, chart 𝔖 k)) ≤ Im by
      intro y
      obtain ⟨x, hx⟩ := RingHom.mem_range.mp (htop (Subring.mem_top y))
      exact ⟨x, hx⟩

    have hscal : ∀ r : R, (pullback f g).presheaf.map (homOfLE (le_top : chart 𝔖 k ≤ ⊤)).op
        ((pullback.fst f g ≫ f).appTop ((Scheme.ΓSpecIso (.of R)).inv r)) ∈ Im := fun r =>
      RingHom.mem_range.mpr ⟨_, app_awayToSection_algebraMap 𝔖.toProj 𝔖.toProj_π k r⟩
    have hrat : ∀ l, rfun 𝔖 k l ∈ Im := fun l => RingHom.mem_range.mpr ⟨_, rfl⟩

    have hseg : ∀ l, rfun 𝔖 k l =
        (pullback f g).presheaf.map (homOfLE hO₁').op (rfun 𝔓' (idx N N' k).1 (idx N N' l).1) *
          (pullback f g).presheaf.map (homOfLE hO₂').op (rfun 𝔔' (idx N N' k).2 (idx N N' l).2) := fun l => by
      have h := rfun_segre_eq 𝔖 hσ k l (le_refl _) hO₁' hO₂'
      rwa [pmap_self] at h

    have hrP : ∀ a, (pullback f g).presheaf.map (homOfLE hO₁').op (rfun 𝔓' (idx N N' k).1 a) =
        (pullback f g).presheaf.map (homOfLE hO₁).op
          ((pullback.fst f g).app (chart 𝔓 (idx N N' k).1) (rfun 𝔓 (idx N N' k).1 a)) := fun a => by
      have e := ConcreteCategory.congr_hom (Scheme.Hom.congr_app hto' (DD R N (idx N N' k).1))
        (Proj.awayToSection _ (MvPolynomial.X (idx N N' k).1) (ProjSpace.ratio R N (idx N N' k).1 a))
      change rfun 𝔓' (idx N N' k).1 a = (pullback f g).presheaf.map _
        ((pullback.fst f g).app (chart 𝔓 (idx N N' k).1) (rfun 𝔓 (idx N N' k).1 a)) at e
      rw [e]
      exact (pmap_pmap _ _ _).trans (pmap_congr _ _ _)
    have hrQ : ∀ b, (pullback f g).presheaf.map (homOfLE hO₂').op (rfun 𝔔' (idx N N' k).2 b) =
        (pullback f g).presheaf.map (homOfLE hO₂).op
          ((pullback.snd f g).app (chart 𝔔 (idx N N' k).2) (rfun 𝔔 (idx N N' k).2 b)) := fun b => by
      have e := ConcreteCategory.congr_hom (Scheme.Hom.congr_app hto₀ (DD R N' (idx N N' k).2))
        (Proj.awayToSection _ (MvPolynomial.X (idx N N' k).2) (ProjSpace.ratio R N' (idx N N' k).2 b))
      change rfun 𝔔' (idx N N' k).2 b = (pullback f g).presheaf.map _
        ((pullback.snd f g).app (chart 𝔔 (idx N N' k).2) (rfun 𝔔 (idx N N' k).2 b)) at e
      rw [e]
      exact (pmap_pmap _ _ _).trans (pmap_congr _ _ _)
    have hrP1 : (pullback f g).presheaf.map (homOfLE hO₁).op
        ((pullback.fst f g).app (chart 𝔓 (idx N N' k).1) (rfun 𝔓 (idx N N' k).1 (idx N N' k).1)) = 1 := by
      rw [rfun, ProjSpace.ratio_self, map_one, map_one, map_one, map_one]
    have hrQ1 : (pullback f g).presheaf.map (homOfLE hO₂).op
        ((pullback.snd f g).app (chart 𝔔 (idx N N' k).2) (rfun 𝔔 (idx N N' k).2 (idx N N' k).2)) = 1 := by
      rw [rfun, ProjSpace.ratio_self, map_one, map_one, map_one, map_one]
    rw [← hgenO, Subring.closure_le]
    rintro y (⟨s, rfl⟩ | ⟨t, rfl⟩)
    ·
      obtain ⟨x, rfl⟩ := 𝔓.toProj.app_surjective (DD R N (idx N N' k).1) (isAffineOpen_DD R N _) s
      let Φ : Γ(PP R N, DD R N (idx N N' k).1) →+* Γ(pullback f g, chart 𝔖 k) :=
        ((pullback f g).presheaf.map (homOfLE hO₁).op).hom.comp
          (((pullback.fst f g).app (chart 𝔓 (idx N N' k).1)).hom.comp (𝔓.toProj.app (DD R N (idx N N' k).1)).hom)
      change Φ x ∈ Im
      have hx := mem_closure_awayToSection R N (idx N N' k).1 x
      suffices hsub : (Subring.closure
          (Set.range (fun r : R => Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
              (MvPolynomial.X (idx N N' k).1) (algebraMap R _ r)) ∪
            Set.range (fun a : Fin (N + 1) => Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
              (MvPolynomial.X (idx N N' k).1) (ProjSpace.ratio R N (idx N N' k).1 a)))).map Φ ≤ Im from
        hsub (Subring.mem_map.mpr ⟨x, hx, rfl⟩)
      rw [RingHom.map_closure, Subring.closure_le]
      rintro _ ⟨w, hw, rfl⟩
      rcases hw with ⟨r, rfl⟩ | ⟨a, rfl⟩
      ·
        change (pullback f g).presheaf.map (homOfLE hO₁).op ((pullback.fst f g).app (chart 𝔓 (idx N N' k).1)
          (𝔓.toProj.app (DD R N (idx N N' k).1) (Proj.awayToSection _ (MvPolynomial.X (idx N N' k).1)
            (algebraMap R _ r)))) ∈ Im
        rw [app_awayToSection_algebraMap 𝔓.toProj 𝔓.toProj_π (idx N N' k).1 r]
        have nat := ConcreteCategory.congr_hom
          (Scheme.Hom.naturality (pullback.fst f g) (homOfLE (le_top : chart 𝔓 (idx N N' k).1 ≤ ⊤)).op)
          (f.appTop ((Scheme.ΓSpecIso (.of R)).inv r))
        change (pullback.fst f g).app (chart 𝔓 (idx N N' k).1)
            (X.presheaf.map (homOfLE (le_top : chart 𝔓 (idx N N' k).1 ≤ ⊤)).op
              (f.appTop ((Scheme.ΓSpecIso (.of R)).inv r))) =
          (pullback f g).presheaf.map
            ((Opens.map (pullback.fst f g).base).map (homOfLE (le_top : chart 𝔓 (idx N N' k).1 ≤ ⊤)).op.unop).op
            ((pullback.fst f g).appTop (f.appTop ((Scheme.ΓSpecIso (.of R)).inv r))) at nat
        rw [nat, pmap_pmap]
        have := hscal r
        rw [Scheme.Hom.comp_appTop] at this
        convert this using 2
        all_goals try rfl
      ·
        change (pullback f g).presheaf.map (homOfLE hO₁).op ((pullback.fst f g).app (chart 𝔓 (idx N N' k).1)
          (rfun 𝔓 (idx N N' k).1 a)) ∈ Im
        have h := hseg ((idx N N').symm (a, (idx N N' k).2))
        rw [Equiv.apply_symm_apply] at h
        change rfun 𝔖 k _ = (pullback f g).presheaf.map (homOfLE hO₁').op (rfun 𝔓' (idx N N' k).1 a) *
          (pullback f g).presheaf.map (homOfLE hO₂').op (rfun 𝔔' (idx N N' k).2 (idx N N' k).2) at h
        rw [hrP, hrQ, hrQ1, mul_one] at h
        rw [← h]
        exact hrat _
    ·
      obtain ⟨x, rfl⟩ := 𝔔.toProj.app_surjective (DD R N' (idx N N' k).2) (isAffineOpen_DD R N' _) t
      let Φ : Γ(PP R N', DD R N' (idx N N' k).2) →+* Γ(pullback f g, chart 𝔖 k) :=
        ((pullback f g).presheaf.map (homOfLE hO₂).op).hom.comp
          (((pullback.snd f g).app (chart 𝔔 (idx N N' k).2)).hom.comp (𝔔.toProj.app (DD R N' (idx N N' k).2)).hom)
      change Φ x ∈ Im
      have hx := mem_closure_awayToSection R N' (idx N N' k).2 x
      suffices hsub : (Subring.closure
          (Set.range (fun r : R => Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) R)
              (MvPolynomial.X (idx N N' k).2) (algebraMap R _ r)) ∪
            Set.range (fun b : Fin (N' + 1) => Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) R)
              (MvPolynomial.X (idx N N' k).2) (ProjSpace.ratio R N' (idx N N' k).2 b)))).map Φ ≤ Im from
        hsub (Subring.mem_map.mpr ⟨x, hx, rfl⟩)
      rw [RingHom.map_closure, Subring.closure_le]
      rintro _ ⟨w, hw, rfl⟩
      rcases hw with ⟨r, rfl⟩ | ⟨b, rfl⟩
      ·
        change (pullback f g).presheaf.map (homOfLE hO₂).op ((pullback.snd f g).app (chart 𝔔 (idx N N' k).2)
          (𝔔.toProj.app (DD R N' (idx N N' k).2) (Proj.awayToSection _ (MvPolynomial.X (idx N N' k).2)
            (algebraMap R _ r)))) ∈ Im
        rw [app_awayToSection_algebraMap 𝔔.toProj 𝔔.toProj_π (idx N N' k).2 r]
        have nat := ConcreteCategory.congr_hom
          (Scheme.Hom.naturality (pullback.snd f g) (homOfLE (le_top : chart 𝔔 (idx N N' k).2 ≤ ⊤)).op)
          (g.appTop ((Scheme.ΓSpecIso (.of R)).inv r))
        change (pullback.snd f g).app (chart 𝔔 (idx N N' k).2)
            (Y.presheaf.map (homOfLE (le_top : chart 𝔔 (idx N N' k).2 ≤ ⊤)).op
              (g.appTop ((Scheme.ΓSpecIso (.of R)).inv r))) =
          (pullback f g).presheaf.map
            ((Opens.map (pullback.snd f g).base).map (homOfLE (le_top : chart 𝔔 (idx N N' k).2 ≤ ⊤)).op.unop).op
            ((pullback.snd f g).appTop (g.appTop ((Scheme.ΓSpecIso (.of R)).inv r))) at nat
        rw [nat, pmap_pmap]
        have := hscal r
        have hc : (pullback.fst f g ≫ f).appTop = (pullback.snd f g ≫ g).appTop := by rw [pullback.condition]
        rw [hc, Scheme.Hom.comp_appTop] at this
        convert this using 2
        all_goals try rfl
      ·
        change (pullback f g).presheaf.map (homOfLE hO₂).op ((pullback.snd f g).app (chart 𝔔 (idx N N' k).2)
          (rfun 𝔔 (idx N N' k).2 b)) ∈ Im
        have h := hseg ((idx N N').symm ((idx N N' k).1, b))
        rw [Equiv.apply_symm_apply] at h
        change rfun 𝔖 k _ = (pullback f g).presheaf.map (homOfLE hO₁').op (rfun 𝔓' (idx N N' k).1 (idx N N' k).1) *
          (pullback f g).presheaf.map (homOfLE hO₂').op (rfun 𝔔' (idx N N' k).2 b) at h
        rw [hrP, hrQ, hrP1, one_mul] at h
        rw [← h]
        exact hrat _
  constructor
  · change IsAffineOpen (chart 𝔖 k)
    rw [hchart]
    exact haff
  · rw [morphismRestrict_appTop]
    have main : ∀ O : (PP R (KK N N')).Opens, O = DD R (KK N N') k → Function.Surjective (𝔖.toProj.app O) := by
      rintro O rfl
      exact core
    exact surjective_comp_eqToHom _ _ (main _ (Scheme.Opens.ι_image_top _))

end Product

end P2mSegreCI

end

theorem solution
    {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    (L : X.Modules) (hL : Scheme.Modules.ClosedImmersionBySections L f)
    (M : Y.Modules) (hM : Scheme.Modules.ClosedImmersionBySections M g) :
    Scheme.Modules.ClosedImmersionBySections
      ((Scheme.Modules.pullback (pullback.fst f g)).obj L ⊗ (Scheme.Modules.pullback (pullback.snd f g)).obj M)
      (pullback.fst f g ≫ f) := by
  obtain ⟨N, 𝔓, hφ⟩ := hL
  obtain ⟨N', 𝔔, hψ⟩ := hM
  exact P2mSegreCI.closedImmersionBySections 𝔓 𝔔 hφ hψ

end S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_fst_tensor_pullback_snd
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_fst_tensor_pullback_snd (solution)
