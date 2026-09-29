-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.FiniteBySections.tensor_monoidalV2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/a86676a5-bacf-5503-94b8-be1a6b1a299f

import Mathlib
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_FiniteBySections_tensor_monoidalV2

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Surjective HasAffineProperty HasAffineProperty.iff_of_iSup_eq_top IsProper Scheme.Hom IsFinite Scheme.preimage_basicOpen Spec Scheme Scheme.mem_basicOpen'' Proj.mem_basicOpen Proj IsSeparated IsFinite.iff_isProper_and_isAffineHom isAffineOpen_top isAffineHom_diagonal_iff Proj.stalkIso' IsProper.of_comp Proj.isAffineOpen_basicOpen Proj.basicOpen IsAffineOpen Scheme.Modules Scheme.Hom.preimage_iSup Proj.iSup_basicOpen_eq_top IsAffineHom Proj.awayToSection Scheme.Modules.map_smul ProjectiveSpectrum.Proj.awayToSection_germ Scheme.Modules.FiniteBySections ProjSpace.π ProjSpace.irrelevant_le_span_X ProjSpace.X_mem_one ProjSpace.ratio Scheme.Modules.tensorSections Scheme.Modules.tensorSections_smul_left Scheme.Modules.tensorSections_smul_right Scheme.Modules.map_homOfLE_tensorSections Scheme.Modules.IsFrameOn Scheme.Modules.IsFrameOn.tensorSections_monoidalV2 Scheme.Modules.exists_projPresentation_of_iSup_eq_top" namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "mem_basicOpen basicOpen_res basicOpen_of_isUnit Hom mk Γ preimage_basicOpen mem_basicOpen'' affineOpens basicOpen Modules Hom.preimage_iSup Opens Modules.map_smul Modules.FiniteBySections Modules.tensorSections Modules.tensorSections_smul_left Modules.tensorSections_smul_right Modules.map_homOfLE_tensorSections Modules.IsFrameOn Modules.IsFrameOn.tensorSections_monoidalV2 Modules.exists_projPresentation_of_iSup_eq_top" namespace Modules p2m_export "AlgebraicGeometry.Scheme.Modules" "pullback presheaf Hom map_smul tensor ProjPresentation FiniteBySections tensorSections tensorSections_smul_left tensorSections_smul_right map_homOfLE_tensorSections IsFrameOn IsFrameOn.tensorSections_monoidalV2 exists_projPresentation_of_iSup_eq_top" namespace IsFrameOn p2m_export "AlgebraicGeometry.Scheme.Modules.IsFrameOn" "mono map tensorSections_monoidalV2" end AlgebraicGeometry.Scheme.Modules.IsFrameOn
namespace AlgebraicGeometry.Scheme.Modules.IsFrameOn
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.IsFrameOn" in
private alias _root_.AlgebraicGeometry.Scheme.Modules.IsFrameOn.tensorSections := AlgebraicGeometry.Scheme.Modules.IsFrameOn.tensorSections_monoidalV2

end AlgebraicGeometry.Scheme.Modules.IsFrameOn
p2m_export "" "AlgebraicGeometry.Scheme.Modules.IsFrameOn.tensorSections"
set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_FiniteBySections_tensor_monoidalV2.AlgebraicGeometry Opposite TopologicalSpace"

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

noncomputable section

namespace P2mSegre

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

variable (𝔓 𝔔)

theorem isSeparated_of_isFinite (hφ : IsFinite 𝔓.toProj) : IsSeparated f := by
  rw [← 𝔓.toProj_π]
  infer_instance

theorem isProper_of_isFinite (hφ : IsFinite 𝔓.toProj) : IsProper f := by
  rw [← 𝔓.toProj_π]
  infer_instance

theorem isAffineOpen_inf (hφ : IsFinite 𝔓.toProj) {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    IsAffineOpen (U ⊓ V) := by
  haveI := isSeparated_of_isFinite 𝔓 hφ
  have hd : IsAffineHom (pullback.diagonal f) := inferInstance
  exact isAffineHom_diagonal_iff.mp hd ⊤ (isAffineOpen_top _) U le_top V le_top hU hV

theorem isAffineOpen_DD (R : Type u) [CommRing R] (N : ℕ) (i : Fin (N + 1)) : IsAffineOpen (DD R N i) :=
  Proj.isAffineOpen_basicOpen _ (MvPolynomial.X i) (ProjSpace.X_mem_one R N i) one_pos

theorem isAffineOpen_chart (hφ : IsFinite 𝔓.toProj) (i : Fin (N + 1)) : IsAffineOpen (chart 𝔓 i) :=
  (isAffineOpen_DD R N i).preimage 𝔓.toProj

theorem finiteBySections_tensor (hφ : IsFinite 𝔓.toProj) (hψ : IsFinite 𝔔.toProj) :
    (L ⊗ M).FiniteBySections f := by
  obtain ⟨𝔖, hσ, hW⟩ := exists_segre 𝔓 𝔔
  refine ⟨_, 𝔖, ?_⟩
  rw [IsFinite.iff_isProper_and_isAffineHom]
  constructor
  · haveI : IsProper (𝔖.toProj ≫ ProjSpace.π R (KK N N')) := by
      rw [𝔖.toProj_π]
      exact isProper_of_isFinite 𝔓 hφ
    exact IsProper.of_comp 𝔖.toProj (ProjSpace.π R (KK N N'))
  · rw [HasAffineProperty.iff_of_iSup_eq_top (P := @IsAffineHom)
      (fun k => (⟨DD R (KK N N') k, isAffineOpen_DD R (KK N N') k⟩ : (PP R (KK N N')).affineOpens))
      (iSup_DD (R := R) (N := KK N N'))]
    intro k
    change IsAffineOpen (chart 𝔖 k)
    have heq : chart 𝔖 k = WW 𝔓 𝔔 k := le_antisymm (chart_segre_le 𝔖 hσ hW k) (hW k)
    rw [heq]
    exact isAffineOpen_inf 𝔓 hφ (isAffineOpen_chart 𝔓 hφ _) (isAffineOpen_chart 𝔔 hψ _)

end Two

end P2mSegre

end

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)}
    {L M : X.Modules} (hL : L.FiniteBySections f) (hM : M.FiniteBySections f) :
    (L ⊗ M).FiniteBySections f := by
  obtain ⟨N, 𝔓, hφ⟩ := hL
  obtain ⟨N', 𝔔, hψ⟩ := hM
  exact P2mSegre.finiteBySections_tensor 𝔓 𝔔 hφ hψ

end S_AlgebraicGeometry_Scheme_Modules_FiniteBySections_tensor_monoidalV2
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_FiniteBySections_tensor_monoidalV2 (solution)
