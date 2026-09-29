-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.FiniteBySections.of_forall_mem_finset_away
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/fb8e326b-9dff-52db-b86d-9299345bbe3c

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_bijective_unit_app_of_le_opensRange
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocalization_basicOpen_of_locallyTrivial_of_qcqs
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_locallyQuasiFinite_of_forall_exists_eq_sum_smul
import Theorems.Thm_AlgebraicGeometry_ProjSpace_isPullback_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_FiniteBySections_of_forall_mem_finset_away

set_option autoImplicit false

universe u

noncomputable section

p2m_open "CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_FiniteBySections_of_forall_mem_finset_away.AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.Hom.app_smul quasiSeparatedSpace_of_quasiSeparated Scheme.Modules.pushforward IsZariskiLocalAtSource.iff_of_openCover IsProper Scheme.Modules.pullback Scheme.Hom quasiSeparatedSpace_of_isAffine Scheme.Modules.Hom LocallyQuasiFinite IsFinite QuasiCompact Scheme.Pullback.range_fst Spec Spec.map Scheme.ΓSpecIso_inv_naturality Scheme Scheme.Hom.preimage_opensRange QuasiCompact.compactSpace_of_compactSpace IsZariskiLocalAtSource IsOpenImmersion Spec.map_base Scheme.Hom.comp_appTop Proj Scheme.Hom.naturality Scheme.Hom.isIso_app Scheme.preimage_basicOpen_top Scheme.Cover.mkOfCovers IsProper.of_comp Scheme.Modules.pullbackPushforwardAdjunction Scheme.Hom.preimage_image_eq Proj.basicOpen Scheme.Modules Proj.iSup_basicOpen_eq_top IsFinite.of_isProper_of_locallyQuasiFinite Scheme.Modules.map_smul Scheme.Hom.image_le_opensRange basicOpen_eq_of_affine Scheme.Cover Scheme.ΓSpecIso Scheme.Hom.coe_opensRange Scheme.Modules.IsInvertible ProjSpace.π ProjSpace.irrelevant_le_span_X ProjSpace.map Scheme.Modules.ProjPresentation Scheme.Modules.FiniteBySections Scheme.Modules.bijective_unit_app_of_le_opensRange Scheme.Modules.isLocalization_basicOpen_of_locallyTrivial_of_qcqs Scheme.Modules.exists_projPresentation_of_iSup_eq_top Scheme.Modules.ProjPresentation.exists_baseChange_of_isPullback Scheme.Modules.ProjPresentation.locallyQuasiFinite_of_forall_exists_eq_sum_smul ProjSpace.isPullback_map"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.Hom.app_smul Modules.pushforward Modules.pullback Hom Γ empty Modules.Hom Pullback.range_fst ΓSpecIso_inv_naturality Hom.preimage_opensRange OpenCover Hom.comp_appTop Hom.naturality basicOpen Hom.isIso_app preimage_basicOpen_top Cover.mkOfCovers Modules.pullbackPushforwardAdjunction Hom.preimage_image_eq Modules Opens Modules.map_smul basicOpen_le Hom.image_le_opensRange PresheafOfModules Cover ΓSpecIso Hom.coe_opensRange Modules.IsInvertible Modules.ProjPresentation Modules.FiniteBySections Modules.bijective_unit_app_of_le_opensRange Modules.isLocalization_basicOpen_of_locallyTrivial_of_qcqs Modules.exists_projPresentation_of_iSup_eq_top Modules.ProjPresentation.exists_baseChange_of_isPullback Modules.ProjPresentation.locallyQuasiFinite_of_forall_exists_eq_sum_smul"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "Hom.app_smul pushforward pullback presheaf Hom isSheaf pullbackPushforwardAdjunction map_smul IsInvertible ProjPresentation FiniteBySections bijective_unit_app_of_le_opensRange isLocalization_basicOpen_of_locallyTrivial_of_qcqs exists_projPresentation_of_iSup_eq_top ProjPresentation.exists_baseChange_of_isPullback ProjPresentation.locallyQuasiFinite_of_forall_exists_eq_sum_smul"
namespace FbsLocal
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

section Generalities

variable {X : Scheme.{u}}

theorem app_naturality {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens} (i : U ⟶ V) (m : Γ(M, V)) :
    N.presheaf.map i.op (φ.app V m) = φ.app U (M.presheaf.map i.op m) := by
  have h := PresheafOfModules.Hom.naturality φ.val i.op
  have h' := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) m
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h'
  exact h'.symm

theorem subsingleton_sections_bot (M : X.Modules) : Subsingleton (Γ(M, (⊥ : X.Opens)) : Type u) := by
  let Msh : TopCat.Sheaf Ab X := ⟨M.presheaf, M.isSheaf⟩
  refine ⟨fun a b => ?_⟩
  exact Msh.eq_of_locally_eq' (fun i : PEmpty.{u + 1} => i.elim) ⊥ (fun i => i.elim) (by simp) a b (fun i => i.elim)

theorem subsingleton_functions_bot : Subsingleton (Γ(X, (⊥ : X.Opens)) : Type u) := by
  refine ⟨fun a b => ?_⟩
  exact X.sheaf.eq_of_locally_eq' (fun i : PEmpty.{u + 1} => i.elim) ⊥ (fun i => i.elim) (by simp) a b (fun i => i.elim)

theorem bijective_smul_of_le_bot (M : X.Modules) {W : X.Opens} (hW : W ≤ ⊥) (s : Γ(M, W)) :
    Function.Bijective fun g : Γ(X, W) => g • s := by
  obtain rfl : W = ⊥ := le_bot_iff.mp hW
  haveI := subsingleton_sections_bot M
  haveI : Subsingleton (Γ(X, (⊥ : X.Opens)) : Type u) := subsingleton_functions_bot
  exact ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨0, Subsingleton.elim _ _⟩⟩

end Generalities

section OpenImm

variable {X X' : Scheme.{u}} (p : X' ⟶ X) [IsOpenImmersion p] (M : X.Modules)

abbrev η : M ⟶ (Scheme.Modules.pushforward p).obj ((Scheme.Modules.pullback p).obj M) :=
  (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M

abbrev pull (V : X.Opens) (m : Γ(M, V)) : Γ((Scheme.Modules.pullback p).obj M, p ⁻¹ᵁ V) := (η p M).app V m

theorem pull_smul (V : X.Opens) (c : Γ(X, V)) (m : Γ(M, V)) :
    pull p M V (c • m) = p.app V c • pull p M V m := by
  rw [pull, Scheme.Modules.Hom.app_smul]
  rfl

theorem map_pull {U V : X.Opens} (h : U ≤ V) (m : Γ(M, V)) :
    ((Scheme.Modules.pullback p).obj M).presheaf.map (homOfLE ((Opens.map p.base).monotone h)).op (pull p M V m)
      = pull p M U (M.presheaf.map (homOfLE h).op m) := by
  rw [pull, pull, ← app_naturality (η p M) (homOfLE h) m]
  rfl

theorem pull_bijective (V : X.Opens) (hV : V ≤ p.opensRange) : Function.Bijective (pull p M V) :=
  Scheme.Modules.bijective_unit_app_of_le_opensRange p M V hV

theorem app_bijective (V : X.Opens) (hV : V ≤ p.opensRange) : Function.Bijective (p.app V) := by
  haveI := Scheme.Hom.isIso_app p V hV
  exact ConcreteCategory.bijective_of_isIso (p.app V)

theorem bijective_smul_of_bijective_smul_pull (σ : Γ(M, ⊤)) {V : X.Opens} (hV : V ≤ p.opensRange)
    (h : ∀ W' : X'.Opens, W' ≤ p ⁻¹ᵁ V →
      Function.Bijective fun g' : Γ(X', W') =>
        g' • ((Scheme.Modules.pullback p).obj M).presheaf.map (homOfLE (le_top : W' ≤ p ⁻¹ᵁ ⊤)).op (pull p M ⊤ σ))
    (W : X.Opens) (hW : W ≤ V) :
    Function.Bijective fun g : Γ(X, W) => g • M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op σ := by
  have hWr : W ≤ p.opensRange := hW.trans hV

  have hsq : (pull p M W) ∘ (fun g : Γ(X, W) => g • M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op σ)
      = (fun g' : Γ(X', p ⁻¹ᵁ W) =>
          g' • ((Scheme.Modules.pullback p).obj M).presheaf.map (homOfLE (le_top : p ⁻¹ᵁ W ≤ p ⁻¹ᵁ ⊤)).op
            (pull p M ⊤ σ)) ∘ (p.app W) := by
    funext g
    simp only [Function.comp_apply]
    rw [pull_smul]
    congr 1
    exact (map_pull p M (le_top : W ≤ ⊤) σ).symm
  have h1 := (h (p ⁻¹ᵁ W) ((Opens.map p.base).monotone hW)).comp (app_bijective p W hWr)
  rw [← hsq] at h1
  exact (Function.Bijective.of_comp_iff' (pull_bijective p M W hWr) _).mp h1

end OpenImm

section Away

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (M : X.Modules) (g : R)

abbrev Sg : Spec (.of (Localization.Away g)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away g)))

abbrev pg := Limits.pullback.fst f (Sg g)
abbrev fg := Limits.pullback.snd f (Sg g)

abbrev gX : Γ(X, ⊤) := f.appTop ((Scheme.ΓSpecIso (.of R)).inv g)

abbrev Ug : X.Opens := X.basicOpen (gX f g)

omit M in
theorem coe_opensRange_Sg : ((Sg g).opensRange : Set (Spec (.of R))) = (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R)) := by
  rw [Scheme.Hom.coe_opensRange]
  have : ⇑(Sg g).base = PrimeSpectrum.comap (algebraMap R (Localization.Away g)) := by
    rw [Spec.map_base]; rfl
  change Set.range ⇑(Sg g).base = _
  rw [this]
  exact PrimeSpectrum.localization_away_comap_range (Localization.Away g) g

theorem preimage_basicOpen_eq_Ug : f ⁻¹ᵁ PrimeSpectrum.basicOpen g = Ug f g := by
  rw [show (PrimeSpectrum.basicOpen g : (Spec (.of R)).Opens)
      = (Spec (.of R)).basicOpen ((Scheme.ΓSpecIso (.of R)).inv g) from (basicOpen_eq_of_affine (R := .of R) g).symm]
  exact Scheme.preimage_basicOpen_top f _

theorem opensRange_pg : (pg f g).opensRange = Ug f g := by
  ext1
  rw [Scheme.Hom.coe_opensRange]
  change Set.range ⇑(pg f g).base = _
  rw [Scheme.Pullback.range_fst, ← Scheme.Hom.coe_opensRange, coe_opensRange_Sg, ← preimage_basicOpen_eq_Ug]
  rfl

theorem preimage_Ug : (pg f g) ⁻¹ᵁ Ug f g = ⊤ := by
  rw [← opensRange_pg]; exact Scheme.Hom.preimage_opensRange _

theorem mem_range_pg_of {x : X} (hx : x ∈ Ug f g) : ∃ y, (pg f g).base y = x := by
  have : x ∈ ((pg f g).opensRange : Set X) := by rw [opensRange_pg]; exact hx
  rwa [Scheme.Hom.coe_opensRange] at this

theorem appTop_pg_gX :
    (pg f g).appTop (gX f g)
      = (fg f g).appTop ((Scheme.ΓSpecIso (.of (Localization.Away g))).inv (algebraMap R (Localization.Away g) g)) := by
  change ((f.appTop ≫ (pg f g).appTop)) ((Scheme.ΓSpecIso (.of R)).inv g) = _
  rw [← Scheme.Hom.comp_appTop, pullback.condition, Scheme.Hom.comp_appTop]
  change (fg f g).appTop ((Sg g).appTop ((Scheme.ΓSpecIso (.of R)).inv g)) = _
  congr 1
  have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (Localization.Away g)))
  have h2 := RingHom.congr_fun (congrArg CommRingCat.Hom.hom this) g
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at h2
  exact h2.symm

theorem isUnit_appTop_pg_gX : IsUnit ((pg f g).appTop (gX f g)) := by
  rw [appTop_pg_gX]
  exact ((IsLocalization.Away.algebraMap_isUnit g).map _).map _

theorem isUnit_res_appTop_pg_gX {W' : (Limits.pullback f (Sg g)).Opens} (hW : W' ≤ ⊤) :
    IsUnit ((Limits.pullback f (Sg g)).presheaf.map (homOfLE hW).op ((pg f g).appTop (gX f g))) :=
  (isUnit_appTop_pg_gX f g).map ((Limits.pullback f (Sg g)).presheaf.map (homOfLE hW).op).hom

theorem res_app_res (n : ℕ) {W' : (Limits.pullback f (Sg g)).Opens} (hle : W' ≤ (pg f g) ⁻¹ᵁ Ug f g) :
    (Limits.pullback f (Sg g)).presheaf.map (homOfLE hle).op
        ((pg f g).app (Ug f g) (X.presheaf.map (homOfLE (X.basicOpen_le (gX f g))).op (gX f g ^ n)))
      = (Limits.pullback f (Sg g)).presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op ((pg f g).appTop (gX f g)) ^ n := by
  have hnat := Scheme.Hom.naturality (pg f g) (homOfLE (X.basicOpen_le (gX f g))).op
  have step : (Limits.pullback f (Sg g)).presheaf.map (homOfLE hle).op
        ((pg f g).app (Ug f g) (X.presheaf.map (homOfLE (X.basicOpen_le (gX f g))).op (gX f g ^ n)))
      = ((X.presheaf.map (homOfLE (X.basicOpen_le (gX f g))).op ≫ (pg f g).app (Ug f g)) ≫
          (Limits.pullback f (Sg g)).presheaf.map (homOfLE hle).op) (gX f g ^ n) := rfl
  rw [step, hnat, Category.assoc, ← Functor.map_comp]
  change (Limits.pullback f (Sg g)).presheaf.map _ ((pg f g).appTop (gX f g ^ n)) = _
  rw [map_pow, map_pow]
  rfl

theorem exists_clear (hinv : Scheme.Modules.IsInvertible M) [CompactSpace X] [QuasiSeparatedSpace X]
    (t : Γ(M, Ug f g)) :
    ∃ (n : ℕ) (m : Γ(M, ⊤)), M.presheaf.map (homOfLE (X.basicOpen_le (gX f g))).op m
      = X.presheaf.map (homOfLE (X.basicOpen_le (gX f g))).op (gX f g ^ n) • t := by
  have hU : IsCompact (((⊤ : X.Opens)) : Set X) := by simpa using isCompact_univ
  have hU' : IsQuasiSeparated (((⊤ : X.Opens)) : Set X) := by simpa using isQuasiSeparated_univ
  exact (Scheme.Modules.isLocalization_basicOpen_of_locallyTrivial_of_qcqs M hinv.exists_trivialization hU hU'
    (gX f g)).1 t

end Away

section Transfer

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (M : X.Modules) (g : R)

local notation "𝒜" n' => MvPolynomial.homogeneousSubmodule (Fin (n' + 1)) R

theorem bijective_smul_smul_of_isUnit {Y : Scheme.{u}} {N : Y.Modules} {W : Y.Opens} (s : Γ(N, W)) (u : Γ(Y, W))
    (hu : IsUnit u) (hs : Function.Bijective fun c : Γ(Y, W) => c • s) :
    Function.Bijective fun c : Γ(Y, W) => c • (u • s) := by
  obtain ⟨uinv, hu1, hu2⟩ : ∃ uinv, u * uinv = 1 ∧ uinv * u = 1 :=
    ⟨((hu.unit⁻¹ : Γ(Y, W)ˣ) : Γ(Y, W)), hu.mul_val_inv, hu.val_inv_mul⟩
  have hb : Function.Bijective (fun c : Γ(Y, W) => c * u) := by
    refine ⟨fun a b h => ?_, fun y => ⟨y * uinv, ?_⟩⟩
    · have := congr_arg (· * uinv) h
      simpa only [mul_assoc, hu1, mul_one] using this
    · simp only [mul_assoc, hu2, mul_one]
  have key : (fun c : Γ(Y, W) => c • (u • s)) = (fun c : Γ(Y, W) => c • s) ∘ fun c => c * u := by
    funext c; simp only [Function.comp_apply, mul_smul]
  rw [key]
  exact hs.comp hb

variable {N' : ℕ}
  (𝔓 : ((Scheme.Modules.pullback (pg f g)).obj M).ProjPresentation (fg f g) N')

abbrev chart' (i : Fin (N' + 1)) : (Limits.pullback f (Sg g)).Opens :=
  𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) (Localization.Away g)) (MvPolynomial.X i)

abbrev chartX (i : Fin (N' + 1)) : X.Opens := (pg f g) ''ᵁ chart' f M g 𝔓 i

theorem exists_t (i : Fin (N' + 1)) :
    ∃ t : Γ(M, Ug f g), pull (pg f g) M (Ug f g) t
      = ((Scheme.Modules.pullback (pg f g)).obj M).presheaf.map (homOfLE (le_top : (pg f g) ⁻¹ᵁ Ug f g ≤ ⊤)).op (𝔓.σ i) :=
  (pull_bijective (pg f g) M (Ug f g) (opensRange_pg f g).ge).2 _

variable (hinv : Scheme.Modules.IsInvertible M) [CompactSpace X] [QuasiSeparatedSpace X]
include hinv

theorem exists_descend (i : Fin (N' + 1)) :
    ∃ (n : ℕ) (m : Γ(M, ⊤)),
      ((Scheme.Modules.pullback (pg f g)).obj M).presheaf.map (homOfLE (le_top : (pg f g) ⁻¹ᵁ Ug f g ≤ ⊤)).op
          (pull (pg f g) M ⊤ m)
        = ((pg f g).app (Ug f g) (X.presheaf.map (homOfLE (X.basicOpen_le (gX f g))).op (gX f g ^ n))) •
          ((Scheme.Modules.pullback (pg f g)).obj M).presheaf.map (homOfLE (le_top : (pg f g) ⁻¹ᵁ Ug f g ≤ ⊤)).op (𝔓.σ i)
      ∧ ∀ W : X.Opens, W ≤ chartX f M g 𝔓 i →
          Function.Bijective fun c : Γ(X, W) => c • M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op m := by
  obtain ⟨t, ht⟩ := exists_t f M g 𝔓 i
  obtain ⟨n, m, hm⟩ := exists_clear f M g hinv t
  have key : ((Scheme.Modules.pullback (pg f g)).obj M).presheaf.map
        (homOfLE (le_top : (pg f g) ⁻¹ᵁ Ug f g ≤ ⊤)).op (pull (pg f g) M ⊤ m)
      = ((pg f g).app (Ug f g) (X.presheaf.map (homOfLE (X.basicOpen_le (gX f g))).op (gX f g ^ n))) •
          ((Scheme.Modules.pullback (pg f g)).obj M).presheaf.map
            (homOfLE (le_top : (pg f g) ⁻¹ᵁ Ug f g ≤ ⊤)).op (𝔓.σ i) := by
    have h1 := map_pull (pg f g) M (X.basicOpen_le (gX f g)) m
    rw [hm, pull_smul, ht] at h1
    exact h1
  refine ⟨n, m, key, ?_⟩

  refine bijective_smul_of_bijective_smul_pull (pg f g) M m (Scheme.Hom.image_le_opensRange _ _) ?_
  intro W' hW'
  rw [Scheme.Hom.preimage_image_eq] at hW'

  have hle : W' ≤ (pg f g) ⁻¹ᵁ Ug f g := by rw [preimage_Ug]; exact le_top
  have hres : ((Scheme.Modules.pullback (pg f g)).obj M).presheaf.map (homOfLE (le_top : W' ≤ (pg f g) ⁻¹ᵁ ⊤)).op
        (pull (pg f g) M ⊤ m)
      = ((Limits.pullback f (Sg g)).presheaf.map (homOfLE hle).op
          ((pg f g).app (Ug f g) (X.presheaf.map (homOfLE (X.basicOpen_le (gX f g))).op (gX f g ^ n)))) •
        ((Scheme.Modules.pullback (pg f g)).obj M).presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op (𝔓.σ i) := by
    have := congrArg (((Scheme.Modules.pullback (pg f g)).obj M).presheaf.map (homOfLE hle).op) key
    rw [Scheme.Modules.map_smul] at this
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp] at this
    exact this
  have hunit : IsUnit ((Limits.pullback f (Sg g)).presheaf.map (homOfLE hle).op
      ((pg f g).app (Ug f g) (X.presheaf.map (homOfLE (X.basicOpen_le (gX f g))).op (gX f g ^ n)))) := by
    rw [res_app_res]
    exact (isUnit_res_appTop_pg_gX f g _).pow n
  change Function.Bijective fun g' : Γ(Limits.pullback f (Sg g), W') =>
    g' • ((Scheme.Modules.pullback (pg f g)).obj M).presheaf.map (homOfLE (le_top : W' ≤ (pg f g) ⁻¹ᵁ ⊤)).op
      (pull (pg f g) M ⊤ m)
  rw [hres]
  exact bijective_smul_smul_of_isUnit _ _ hunit (𝔓.frame i W' hW')

end Transfer

section Main

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (M : X.Modules) (g : R)

theorem exists_mem_chart' {N' : ℕ} (𝔓 : ((Scheme.Modules.pullback (pg f g)).obj M).ProjPresentation (fg f g) N')
    (y : ↑(Limits.pullback f (Sg g))) : ∃ i, y ∈ chart' f M g 𝔓 i := by
  have h : ⨆ i : Fin (N' + 1), Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) (Localization.Away g))
      (MvPolynomial.X i) = ⊤ :=
    Proj.iSup_basicOpen_eq_top _ (fun i => MvPolynomial.X i) (ProjSpace.irrelevant_le_span_X (Localization.Away g) N')
  have hx : 𝔓.toProj.base y ∈ (⊤ : (Proj (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) (Localization.Away g))).Opens) :=
    trivial
  rw [← h] at hx
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  exact ⟨i, hi⟩

theorem map_injective_of_eq {Y : Scheme.{u}} (N : Y.Modules) {W W' : Y.Opens} (h : W = W') (hle : W ≤ W') :
    Function.Injective (N.presheaf.map (homOfLE hle).op) := by
  subst h
  intro a b hab
  have : (homOfLE hle) = 𝟙 W := rfl
  rw [this, op_id, N.presheaf.map_id] at hab
  exact hab

theorem exists_coeff (n : ℕ) :
    ∃ c₀ : Localization.Away g,
      (fg f g).appTop ((Scheme.ΓSpecIso (.of (Localization.Away g))).inv c₀) * (pg f g).appTop (gX f g) ^ n = 1 := by
  have hu := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away g) g
  refine ⟨((hu.unit⁻¹ : (Localization.Away g)ˣ) : Localization.Away g) ^ n, ?_⟩
  rw [appTop_pg_gX, ← map_pow, ← map_pow, ← map_mul, ← map_mul, ← mul_pow, hu.val_inv_mul, one_pow, map_one, map_one]

variable [IsProper f] (hinv : Scheme.Modules.IsInvertible M) (s : Finset R) (hs : Ideal.span (s : Set R) = ⊤)
  (h : ∀ g ∈ s, Scheme.Modules.FiniteBySections
      ((Scheme.Modules.pullback (Limits.pullback.fst f
          (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away g)))))).obj M)
      (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away g))))))
include hinv hs h

omit hinv h in

theorem exists_mem_Ug (x : X) : ∃ g ∈ s, x ∈ Ug f g := by
  have hcov : ⨆ g : s, PrimeSpectrum.basicOpen (g : R) = ⊤ := by
    rw [PrimeSpectrum.iSup_basicOpen_eq_top_iff, Subtype.range_coe_subtype]
    simpa using hs
  have hx : f.base x ∈ ⨆ g : s, PrimeSpectrum.basicOpen (g : R) := by
    have : f.base x ∈ ((⨆ g : s, PrimeSpectrum.basicOpen (g : R) : TopologicalSpace.Opens (PrimeSpectrum R)) : Set (PrimeSpectrum R)) := by
      rw [hcov, Opens.coe_top]; exact Set.mem_univ _
    exact this
  obtain ⟨⟨g, hg⟩, hgx⟩ := Opens.mem_iSup.mp hx
  refine ⟨g, hg, ?_⟩
  rw [← preimage_basicOpen_eq_Ug]
  exact hgx

theorem finiteBySections : Scheme.Modules.FiniteBySections M f := by
  classical
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  haveI : QuasiSeparatedSpace X := by
    haveI := quasiSeparatedSpace_of_isAffine (Spec (.of R))
    exact quasiSeparatedSpace_of_quasiSeparated f

  choose Ng 𝔓g hfin using h
  choose nn mm hmm hfr using fun (gg : s) (i : Fin (Ng gg gg.2 + 1)) =>
    exists_descend f M (gg : R) (𝔓g gg gg.2) hinv i

  let I : Type u := Σ gg : s, Fin (Ng gg gg.2 + 1)
  let N : ℕ := Fintype.card I
  have hcard : Fintype.card (Option I) = N + 1 := Fintype.card_option
  let e : Fin (N + 1) ≃ Option I := (finCongr hcard.symm).trans (Fintype.equivFin (Option I)).symm
  let σ' : Fin (N + 1) → Γ(M, ⊤) := fun k => (e k).elim 0 (fun gi => mm gi.1 gi.2)
  let U' : Fin (N + 1) → X.Opens := fun k => (e k).elim ⊥ (fun gi => chartX f M (gi.1 : R) (𝔓g gi.1 gi.1.2) gi.2)
  have hσ'some : ∀ gi : I, σ' (e.symm (some gi)) = mm gi.1 gi.2 := fun gi => by
    simp only [σ', Equiv.apply_symm_apply, Option.elim]
  have hU'some : ∀ gi : I, U' (e.symm (some gi)) = chartX f M (gi.1 : R) (𝔓g gi.1 gi.1.2) gi.2 := fun gi => by
    simp only [U', Equiv.apply_symm_apply, Option.elim]

  have hframe : ∀ k (V : X.Opens), V ≤ U' k →
      Function.Bijective fun c : Γ(X, V) => c • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (σ' k) : Γ(M, V)) := by
    intro k V hV
    rcases hk : e k with _ | gi
    · have hV' : V ≤ ⊥ := by simpa [U', hk] using hV
      exact bijective_smul_of_le_bot M hV' _
    · have h1 : σ' k = mm gi.1 gi.2 := by simp only [σ', hk, Option.elim]
      have h2 : U' k = chartX f M (gi.1 : R) (𝔓g gi.1 gi.1.2) gi.2 := by simp only [U', hk, Option.elim]
      rw [h1]
      rw [h2] at hV
      exact hfr gi.1 gi.2 V hV
  have hU : iSup U' = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨g, hg, hx⟩ := exists_mem_Ug f s hs x
    obtain ⟨y, rfl⟩ := mem_range_pg_of f g hx
    obtain ⟨i, hi⟩ := exists_mem_chart' f M g (𝔓g g hg) y
    refine Opens.mem_iSup.mpr ⟨e.symm (some ⟨⟨g, hg⟩, i⟩), ?_⟩
    rw [hU'some]
    exact ⟨y, hi, rfl⟩

  obtain ⟨𝔔, hσ, hUQ⟩ :=
    Scheme.Modules.exists_projPresentation_of_iSup_eq_top f M N σ' U' hU hframe
  refine ⟨N, 𝔔, ?_⟩

  haveI hprop : IsProper 𝔔.toProj := by
    have : IsProper (𝔔.toProj ≫ ProjSpace.π R N) := by rw [𝔔.toProj_π]; infer_instance
    exact IsProper.of_comp 𝔔.toProj (ProjSpace.π R N)

  haveI hlqf : LocallyQuasiFinite 𝔔.toProj := by
    let 𝒰 : X.OpenCover := Scheme.Cover.mkOfCovers (J := s) (fun gg => Limits.pullback f (Sg (gg : R)))
      (fun gg => pg f (gg : R)) (fun x => by
        obtain ⟨g, hg, hx⟩ := exists_mem_Ug f s hs x
        obtain ⟨y, hy⟩ := mem_range_pg_of f g hx
        exact ⟨⟨g, hg⟩, y, hy⟩)
    refine (IsZariskiLocalAtSource.iff_of_openCover (P := @LocallyQuasiFinite) 𝒰).mpr fun gg => ?_
    obtain ⟨g, hg⟩ := gg
    change LocallyQuasiFinite (pg f g ≫ 𝔔.toProj)
    obtain ⟨𝔔g, hσg, hcomp, -⟩ := Scheme.Modules.ProjPresentation.exists_baseChange_of_isPullback
      (IsPullback.of_hasPullback f (Sg g)) 𝔔
    rw [← hcomp]
    haveI : IsFinite (𝔓g g hg).toProj := hfin g hg
    haveI : LocallyQuasiFinite 𝔔g.toProj := by
      refine Scheme.Modules.ProjPresentation.locallyQuasiFinite_of_forall_exists_eq_sum_smul (𝔓g g hg) 𝔔g fun i => ?_
      obtain ⟨c₀, hc₀⟩ := exists_coeff f g (nn ⟨g, hg⟩ i)
      let k₀ : Fin (N + 1) := e.symm (some ⟨⟨g, hg⟩, i⟩)
      refine ⟨Pi.single k₀ c₀, ?_⟩
      rw [Finset.sum_eq_single k₀]
      · rw [Pi.single_eq_same, hσg, hσ]

        apply map_injective_of_eq _ (preimage_Ug f g) (le_top : (pg f g) ⁻¹ᵁ Ug f g ≤ ⊤)
        have hk : σ' k₀ = mm ⟨g, hg⟩ i := hσ'some ⟨⟨g, hg⟩, i⟩
        rw [Scheme.Modules.map_smul]
        change _ = _ • ((Scheme.Modules.pullback (pg f g)).obj M).presheaf.map
          (homOfLE (le_top : (pg f g) ⁻¹ᵁ Ug f g ≤ ⊤)).op (pull (pg f g) M ⊤ (σ' k₀))
        rw [hk, (hmm ⟨g, hg⟩ i), smul_smul]
        have hB : (pg f g).app (Ug f g) (X.presheaf.map (homOfLE (X.basicOpen_le (gX f g))).op (gX f g ^ nn ⟨g, hg⟩ i))
            = (Limits.pullback f (Sg g)).presheaf.map (homOfLE (le_top : (pg f g) ⁻¹ᵁ Ug f g ≤ ⊤)).op
                ((pg f g).appTop (gX f g)) ^ nn ⟨g, hg⟩ i := by
          have := res_app_res f g (nn ⟨g, hg⟩ i) (le_rfl : (pg f g) ⁻¹ᵁ Ug f g ≤ (pg f g) ⁻¹ᵁ Ug f g)
          rw [show homOfLE (le_rfl : (pg f g) ⁻¹ᵁ Ug f g ≤ (pg f g) ⁻¹ᵁ Ug f g) = 𝟙 _ from rfl, op_id,
            CategoryTheory.Functor.map_id] at this
          simpa using this
        rw [hB, ← map_pow, ← map_mul, hc₀, map_one, one_smul]
      · intro k _ hk
        rw [Pi.single_eq_of_ne hk, map_zero, map_zero, zero_smul]
      · intro hk; exact absurd (Finset.mem_univ _) hk
    haveI : IsOpenImmersion (ProjSpace.map R (Localization.Away g) N) :=
      MorphismProperty.of_isPullback (P := @IsOpenImmersion)
        (ProjSpace.isPullback_map R (Localization.Away g) N).flip inferInstance
    infer_instance
  exact IsFinite.of_isProper_of_locallyQuasiFinite 𝔔.toProj

end Main

end AlgebraicGeometry.Scheme.Modules.FbsLocal

end

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_FiniteBySections_of_forall_mem_finset_away.AlgebraicGeometry in
theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f]
    (M : X.Modules) (hinv : Scheme.Modules.IsInvertible M)
    (s : Finset R) (hs : Ideal.span (s : Set R) = ⊤)
    (h : ∀ g ∈ s, Scheme.Modules.FiniteBySections
        ((Scheme.Modules.pullback (Limits.pullback.fst f
            (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away g)))))).obj M)
        (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away g)))))) :
    Scheme.Modules.FiniteBySections M f :=
  Scheme.Modules.FbsLocal.finiteBySections f M hinv s hs h

end S_AlgebraicGeometry_Scheme_Modules_FiniteBySections_of_forall_mem_finset_away
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_FiniteBySections_of_forall_mem_finset_away (solution)
