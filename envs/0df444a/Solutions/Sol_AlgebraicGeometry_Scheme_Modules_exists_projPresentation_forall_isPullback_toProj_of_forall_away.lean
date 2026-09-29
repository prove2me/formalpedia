-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.exists_projPresentation_forall_isPullback_toProj_of_forall_away
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/cbdd1d4b-9142-5934-8238-d391736c766c

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_bijective_unit_app_of_le_opensRange
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocalization_basicOpen_of_locallyTrivial_of_qcqs
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_forall_isPullback_toProj_of_forall_away

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

noncomputable section

p2m_open "CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_forall_isPullback_toProj_of_forall_away.AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.Hom.app_smul quasiSeparatedSpace_of_quasiSeparated Scheme.Modules.pushforward IsProper Scheme.Modules.pullback Scheme.Hom IsOpenImmersion.of_isLocalization quasiSeparatedSpace_of_isAffine Scheme.Modules.Hom QuasiCompact Scheme.Pullback.range_fst Scheme.homeoOfIso Spec Spec.map Scheme.ΓSpecIso_inv_naturality Scheme Scheme.Modules.Hom.id_app Scheme.Hom.preimage_opensRange Scheme.Hom.appTop QuasiCompact.compactSpace_of_compactSpace IsOpenImmersion Spec.map_base Scheme.Hom.comp_base Scheme.Hom.comp_appTop Proj Scheme.Hom.naturality Scheme.Hom.isIso_app Scheme.preimage_basicOpen_top Scheme.Modules.pullbackPushforwardAdjunction Scheme.Hom.preimage_image_eq Proj.basicOpen Scheme.Modules Scheme.Hom.app_eq_appLE Proj.iSup_basicOpen_eq_top Scheme.Modules.map_smul Scheme.Hom.image_le_opensRange basicOpen_eq_of_affine Scheme.ΓSpecIso Scheme.Hom.coe_opensRange Scheme.Modules.IsInvertible Scheme.Modules.ProjPresentation ProjSpace.irrelevant_le_span_X ProjSpace.map Scheme.Modules.bijective_unit_app_of_le_opensRange Scheme.Modules.isLocalization_basicOpen_of_locallyTrivial_of_qcqs Scheme.Modules.exists_projPresentation_of_iSup_eq_top Scheme.Modules.ProjPresentation.exists_baseChange_of_isPullback Scheme.Modules.ProjPresentation.exists_of_iso"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.Hom.app_smul Modules.pushforward Modules.pullback Hom.id_app Hom Γ empty Modules.Hom Pullback.range_fst homeoOfIso ΓSpecIso_inv_naturality Modules.Hom.id_app Hom.preimage_opensRange Hom.appTop Hom.comp_base Hom.comp_appTop Hom.naturality basicOpen Hom.isIso_app preimage_basicOpen_top Modules.pullbackPushforwardAdjunction Hom.preimage_image_eq Modules Opens Hom.app_eq_appLE Modules.map_smul basicOpen_le Hom.image_le_opensRange PresheafOfModules ΓSpecIso Hom.coe_opensRange Modules.IsInvertible Modules.ProjPresentation Modules.bijective_unit_app_of_le_opensRange Modules.isLocalization_basicOpen_of_locallyTrivial_of_qcqs Modules.exists_projPresentation_of_iSup_eq_top Modules.ProjPresentation.exists_baseChange_of_isPullback Modules.ProjPresentation.exists_of_iso"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "Hom.app_smul pushforward pullback presheaf Hom Hom.id_app isSheaf pullbackPushforwardAdjunction map_smul IsInvertible ProjPresentation FiniteBySections bijective_unit_app_of_le_opensRange isLocalization_basicOpen_of_locallyTrivial_of_qcqs exists_projPresentation_of_iSup_eq_top ProjPresentation.exists_baseChange_of_isPullback ProjPresentation.exists_of_iso"
namespace GlobalPresLocal
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

theorem coef_eq {B : Type u} [CommRing B] (f : X ⟶ Spec (.of B)) (c : B) :
    (f.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (.of B)).inv.hom c) = f.appTop ((Scheme.ΓSpecIso (.of B)).inv c) := by
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

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

variable {S B : Type u} [CommRing S] [CommRing B] [Algebra S B] (r : S) [IsLocalization.Away r B]
  {X X' : Scheme.{u}} (f : X ⟶ Spec (.of S)) (f' : X' ⟶ Spec (.of B)) (p : X' ⟶ X)
  (hp : IsPullback p f' f (Spec.map (CommRingCat.ofHom (algebraMap S B))))
  (M : X.Modules)

abbrev SB : Spec (.of B) ⟶ Spec (.of S) :=
  Spec.map (CommRingCat.ofHom (algebraMap S B))

include r in
theorem isOpenImmersion_SB : IsOpenImmersion (SB (S := S) (B := B)) :=
  IsOpenImmersion.of_isLocalization r

include r hp in

theorem isOpenImmersion_p : IsOpenImmersion p :=
  haveI := isOpenImmersion_SB (B := B) r
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) hp.flip this

abbrev gX : Γ(X, ⊤) := f.appTop ((Scheme.ΓSpecIso (.of S)).inv r)

abbrev Ug : X.Opens := X.basicOpen (gX r f)

theorem coe_opensRange_SB :
    haveI := isOpenImmersion_SB (B := B) r
    ((SB (S := S) (B := B)).opensRange : Set (Spec (.of S))) = (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum S)) := by
  rw [Scheme.Hom.coe_opensRange]
  have : ⇑(SB (S := S) (B := B)).base = PrimeSpectrum.comap (algebraMap S B) := by
    rw [Spec.map_base]; rfl
  change Set.range ⇑(SB (S := S) (B := B)).base = _
  rw [this]
  exact PrimeSpectrum.localization_away_comap_range B r

theorem preimage_basicOpen_eq_Ug : f ⁻¹ᵁ PrimeSpectrum.basicOpen r = Ug r f := by
  rw [show (PrimeSpectrum.basicOpen r : (Spec (.of S)).Opens)
      = (Spec (.of S)).basicOpen ((Scheme.ΓSpecIso (.of S)).inv r) from (basicOpen_eq_of_affine (R := .of S) r).symm]
  exact Scheme.preimage_basicOpen_top f _

include hp in

theorem range_p_base :
    Set.range ⇑p.base = Set.range ⇑(pullback.fst f (SB (S := S) (B := B))).base := by
  rw [← hp.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp]
  exact (Scheme.homeoOfIso hp.isoPullback).surjective.range_comp _

include hp in
theorem opensRange_p [IsOpenImmersion p] : p.opensRange = Ug r f := by
  haveI := isOpenImmersion_SB (B := B) r
  ext1
  rw [Scheme.Hom.coe_opensRange]
  change Set.range ⇑p.base = _
  rw [range_p_base f f' p hp, Scheme.Pullback.range_fst, ← Scheme.Hom.coe_opensRange, coe_opensRange_SB (B := B) r,
    ← preimage_basicOpen_eq_Ug]
  rfl

include hp in
theorem preimage_Ug [IsOpenImmersion p] : p ⁻¹ᵁ Ug r f = ⊤ := by
  rw [← opensRange_p r f f' p hp]; exact Scheme.Hom.preimage_opensRange _

include hp in
theorem mem_range_p_of [IsOpenImmersion p] {x : X} (hx : x ∈ Ug r f) : ∃ y, p.base y = x := by
  have : x ∈ (p.opensRange : Set X) := by rw [opensRange_p r f f' p hp]; exact hx
  rwa [Scheme.Hom.coe_opensRange] at this

include hp in

theorem appTop_p_gX :
    p.appTop (gX r f) = f'.appTop ((Scheme.ΓSpecIso (.of B)).inv (algebraMap S B r)) := by
  change ((f.appTop ≫ p.appTop)) ((Scheme.ΓSpecIso (.of S)).inv r) = _
  rw [← Scheme.Hom.comp_appTop, hp.w, Scheme.Hom.comp_appTop]
  change f'.appTop ((SB (S := S) (B := B)).appTop ((Scheme.ΓSpecIso (.of S)).inv r)) = _
  congr 1
  have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap S B))
  have h2 := RingHom.congr_fun (congrArg CommRingCat.Hom.hom this) r
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at h2
  exact h2.symm

include hp in

theorem isUnit_appTop_p_gX : IsUnit (p.appTop (gX r f)) := by
  rw [appTop_p_gX r f f' p hp]
  exact ((IsLocalization.Away.algebraMap_isUnit (S := B) r).map _).map _

include hp in

theorem isUnit_res_appTop_p_gX {W' : X'.Opens} (hW : W' ≤ ⊤) :
    IsUnit (X'.presheaf.map (homOfLE hW).op (p.appTop (gX r f))) :=
  (isUnit_appTop_p_gX r f f' p hp).map (X'.presheaf.map (homOfLE hW).op).hom

theorem res_app_res (n : ℕ) {W' : X'.Opens} (hle : W' ≤ p ⁻¹ᵁ Ug r f) :
    X'.presheaf.map (homOfLE hle).op
        (p.app (Ug r f) (X.presheaf.map (homOfLE (X.basicOpen_le (gX r f))).op (gX r f ^ n)))
      = X'.presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op (p.appTop (gX r f)) ^ n := by
  have hnat := Scheme.Hom.naturality p (homOfLE (X.basicOpen_le (gX r f))).op
  have step : X'.presheaf.map (homOfLE hle).op
        (p.app (Ug r f) (X.presheaf.map (homOfLE (X.basicOpen_le (gX r f))).op (gX r f ^ n)))
      = ((X.presheaf.map (homOfLE (X.basicOpen_le (gX r f))).op ≫ p.app (Ug r f)) ≫
          X'.presheaf.map (homOfLE hle).op) (gX r f ^ n) := rfl
  rw [step, hnat, Category.assoc, ← Functor.map_comp]
  change X'.presheaf.map _ (p.appTop (gX r f ^ n)) = _
  rw [map_pow, map_pow]
  rfl

theorem exists_clear (hinv : Scheme.Modules.IsInvertible M) [CompactSpace X] [QuasiSeparatedSpace X]
    (t : Γ(M, Ug r f)) :
    ∃ (n : ℕ) (m : Γ(M, ⊤)), M.presheaf.map (homOfLE (X.basicOpen_le (gX r f))).op m
      = X.presheaf.map (homOfLE (X.basicOpen_le (gX r f))).op (gX r f ^ n) • t := by
  have hU : IsCompact (((⊤ : X.Opens)) : Set X) := by simpa using isCompact_univ
  have hU' : IsQuasiSeparated (((⊤ : X.Opens)) : Set X) := by simpa using isQuasiSeparated_univ
  exact (Scheme.Modules.isLocalization_basicOpen_of_locallyTrivial_of_qcqs M hinv.exists_trivialization hU hU'
    (gX r f)).1 t

end Away

section Transfer

variable {S B : Type u} [CommRing S] [CommRing B] [Algebra S B] (r : S) [IsLocalization.Away r B]
  {X X' : Scheme.{u}} (f : X ⟶ Spec (.of S)) (f' : X' ⟶ Spec (.of B)) (p : X' ⟶ X) [IsOpenImmersion p]
  (hp : IsPullback p f' f (Spec.map (CommRingCat.ofHom (algebraMap S B))))
  (M : X.Modules)

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
  (𝔓 : ((Scheme.Modules.pullback p).obj M).ProjPresentation f' N')

abbrev chart' (i : Fin (N' + 1)) : X'.Opens :=
  𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) B) (MvPolynomial.X i)

abbrev chartX (i : Fin (N' + 1)) : X.Opens := p ''ᵁ chart' f' p M 𝔓 i

include hp in

theorem exists_t (i : Fin (N' + 1)) :
    ∃ t : Γ(M, Ug r f), pull p M (Ug r f) t
      = ((Scheme.Modules.pullback p).obj M).presheaf.map (homOfLE (le_top : p ⁻¹ᵁ Ug r f ≤ ⊤)).op (𝔓.σ i) :=
  (pull_bijective p M (Ug r f) (opensRange_p r f f' p hp).ge).2 _

theorem exists_mem_chart' (y : X') : ∃ i, y ∈ chart' f' p M 𝔓 i := by
  have h : ⨆ i : Fin (N' + 1), Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) B)
      (MvPolynomial.X i) = ⊤ :=
    Proj.iSup_basicOpen_eq_top _ (fun i => MvPolynomial.X i) (ProjSpace.irrelevant_le_span_X B N')
  have hx : 𝔓.toProj.base y ∈ (⊤ : (Proj (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) B)).Opens) :=
    trivial
  rw [← h] at hx
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  exact ⟨i, hi⟩

include hp in

theorem exists_coeff (n : ℕ) :
    ∃ c₀ : B, f'.appTop ((Scheme.ΓSpecIso (.of B)).inv c₀) * p.appTop (gX r f) ^ n = 1 := by
  have hu := IsLocalization.Away.algebraMap_isUnit (S := B) r
  refine ⟨((hu.unit⁻¹ : Bˣ) : B) ^ n, ?_⟩
  rw [appTop_p_gX r f f' p hp, ← map_pow, ← map_pow, ← map_mul, ← map_mul, ← mul_pow, hu.val_inv_mul, one_pow,
    map_one, map_one]

variable (hinv : Scheme.Modules.IsInvertible M) [CompactSpace X] [QuasiSeparatedSpace X]
include hinv hp

theorem exists_descend (i : Fin (N' + 1)) :
    ∃ (n : ℕ) (m : Γ(M, ⊤)),
      ((Scheme.Modules.pullback p).obj M).presheaf.map (homOfLE (le_top : p ⁻¹ᵁ Ug r f ≤ ⊤)).op
          (pull p M ⊤ m)
        = (p.app (Ug r f) (X.presheaf.map (homOfLE (X.basicOpen_le (gX r f))).op (gX r f ^ n))) •
          ((Scheme.Modules.pullback p).obj M).presheaf.map (homOfLE (le_top : p ⁻¹ᵁ Ug r f ≤ ⊤)).op (𝔓.σ i)
      ∧ ∀ W : X.Opens, W ≤ chartX f' p M 𝔓 i →
          Function.Bijective fun c : Γ(X, W) => c • M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op m := by
  obtain ⟨t, ht⟩ := exists_t r f f' p hp M 𝔓 i
  obtain ⟨n, m, hm⟩ := exists_clear r f M hinv t
  have key : ((Scheme.Modules.pullback p).obj M).presheaf.map
        (homOfLE (le_top : p ⁻¹ᵁ Ug r f ≤ ⊤)).op (pull p M ⊤ m)
      = (p.app (Ug r f) (X.presheaf.map (homOfLE (X.basicOpen_le (gX r f))).op (gX r f ^ n))) •
          ((Scheme.Modules.pullback p).obj M).presheaf.map
            (homOfLE (le_top : p ⁻¹ᵁ Ug r f ≤ ⊤)).op (𝔓.σ i) := by
    have h1 := map_pull p M (X.basicOpen_le (gX r f)) m
    rw [hm, pull_smul, ht] at h1
    exact h1
  refine ⟨n, m, key, ?_⟩

  refine bijective_smul_of_bijective_smul_pull p M m (Scheme.Hom.image_le_opensRange _ _) ?_
  intro W' hW'
  rw [Scheme.Hom.preimage_image_eq] at hW'

  have hle : W' ≤ p ⁻¹ᵁ Ug r f := by rw [preimage_Ug r f f' p hp]; exact le_top
  have hres : ((Scheme.Modules.pullback p).obj M).presheaf.map (homOfLE (le_top : W' ≤ p ⁻¹ᵁ ⊤)).op
        (pull p M ⊤ m)
      = (X'.presheaf.map (homOfLE hle).op
          (p.app (Ug r f) (X.presheaf.map (homOfLE (X.basicOpen_le (gX r f))).op (gX r f ^ n)))) •
        ((Scheme.Modules.pullback p).obj M).presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op (𝔓.σ i) := by
    have := congrArg (((Scheme.Modules.pullback p).obj M).presheaf.map (homOfLE hle).op) key
    rw [Scheme.Modules.map_smul] at this
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp] at this
    exact this
  have hunit : IsUnit (X'.presheaf.map (homOfLE hle).op
      (p.app (Ug r f) (X.presheaf.map (homOfLE (X.basicOpen_le (gX r f))).op (gX r f ^ n)))) := by
    rw [res_app_res r f p]
    exact (isUnit_res_appTop_p_gX r f f' p hp _).pow n
  change Function.Bijective fun g' : Γ(X', W') =>
    g' • ((Scheme.Modules.pullback p).obj M).presheaf.map (homOfLE (le_top : W' ≤ p ⁻¹ᵁ ⊤)).op
      (pull p M ⊤ m)
  rw [hres]
  exact bijective_smul_smul_of_isUnit _ _ hunit (𝔓.frame i W' hW')

end Transfer

section Main

theorem map_injective_of_eq {Y : Scheme.{u}} (N : Y.Modules) {W W' : Y.Opens} (h : W = W') (hle : W ≤ W') :
    Function.Injective (N.presheaf.map (homOfLE hle).op) := by
  subst h
  intro a b hab
  have : (homOfLE hle) = 𝟙 W := rfl
  rw [this, op_id, N.presheaf.map_id] at hab
  exact hab

variable {S : Type u} [CommRing S] {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
    (B : Fin k → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra S (B i)] [∀ i, IsLocalization.Away (r i) (B i)]
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S))
    {A' : Fin k → Scheme.{u}} (f' : ∀ i, A' i ⟶ Spec (CommRingCat.of (B i))) (g : ∀ i, A' i ⟶ A)
    (hg : ∀ i, IsPullback (g i) (f' i) f (Spec.map (CommRingCat.ofHom (algebraMap S (B i)))))
    (hf : IsProper f) (M : A.Modules) (hM : Scheme.Modules.IsInvertible M)
    (M' : ∀ i, (A' i).Modules) (e : ∀ i, (Scheme.Modules.pullback (g i)).obj M ≅ M' i)
    (N' : Fin k → ℕ) (𝔔 : ∀ i, Scheme.Modules.ProjPresentation (M' i) (f' i) (N' i))

include hr in

theorem exists_mem_Ug (x : A) : ∃ i, x ∈ Ug (r i) f := by
  have hcov : ⨆ i, PrimeSpectrum.basicOpen (r i) = ⊤ := by
    rw [PrimeSpectrum.iSup_basicOpen_eq_top_iff]
    exact hr
  have hx : f.base x ∈ ⨆ i, PrimeSpectrum.basicOpen (r i) := by
    have : f.base x ∈ ((⨆ i, PrimeSpectrum.basicOpen (r i) : TopologicalSpace.Opens (PrimeSpectrum S)) :
        Set (PrimeSpectrum S)) := by
      rw [hcov, Opens.coe_top]; exact Set.mem_univ _
    exact this
  obtain ⟨i, hix⟩ := Opens.mem_iSup.mp hx
  refine ⟨i, ?_⟩
  rw [← preimage_basicOpen_eq_Ug]
  exact hix

include hr hg hf hM e 𝔔 in
theorem main :
    ∃ (N : ℕ) (𝔓 : Scheme.Modules.ProjPresentation M f N),
      ∀ i, ∃ 𝔓' : Scheme.Modules.ProjPresentation (M' i) (f' i) N,
        IsPullback (g i) 𝔓'.toProj 𝔓.toProj (ProjSpace.map S (B i) N) ∧
        ∀ j : Fin (N' i + 1), ∃ a : Fin (N + 1) → B i,
          (𝔔 i).σ j = ∑ l, (((f' i).appLE ⊤ ⊤ le_top).hom
            ((Scheme.ΓSpecIso (CommRingCat.of (B i))).inv.hom (a l))) • 𝔓'.σ l := by
  classical
  haveI := hf
  haveI : CompactSpace A := QuasiCompact.compactSpace_of_compactSpace f
  haveI : QuasiSeparatedSpace A := by
    haveI := quasiSeparatedSpace_of_isAffine (Spec (.of S))
    exact quasiSeparatedSpace_of_quasiSeparated f
  haveI hgi : ∀ i, IsOpenImmersion (g i) := fun i => isOpenImmersion_p (r i) f (f' i) (g i) (hg i)

  choose 𝔔₀ h𝔔₀t h𝔔₀σ using fun i => Scheme.Modules.ProjPresentation.exists_of_iso (𝔔 i) (e i).symm

  choose nn mm hmm hfr using fun (i : Fin k) (j : Fin (N' i + 1)) =>
    exists_descend (r i) f (f' i) (g i) (hg i) M (𝔔₀ i) hM j

  let I : Type := Σ i : Fin k, Fin (N' i + 1)
  let N : ℕ := Fintype.card I
  have hcard : Fintype.card (Option I) = N + 1 := Fintype.card_option
  let eN : Fin (N + 1) ≃ Option I := (finCongr hcard.symm).trans (Fintype.equivFin (Option I)).symm
  let σ' : Fin (N + 1) → Γ(M, ⊤) := fun l => (eN l).elim 0 (fun ij => mm ij.1 ij.2)
  let U' : Fin (N + 1) → A.Opens := fun l => (eN l).elim ⊥ (fun ij => chartX (f' ij.1) (g ij.1) M (𝔔₀ ij.1) ij.2)
  have hσ'some : ∀ ij : I, σ' (eN.symm (some ij)) = mm ij.1 ij.2 := fun ij => by
    simp only [σ', Equiv.apply_symm_apply, Option.elim]
  have hU'some : ∀ ij : I, U' (eN.symm (some ij)) = chartX (f' ij.1) (g ij.1) M (𝔔₀ ij.1) ij.2 := fun ij => by
    simp only [U', Equiv.apply_symm_apply, Option.elim]

  have hframe : ∀ l (V : A.Opens), V ≤ U' l →
      Function.Bijective fun c : Γ(A, V) => c • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (σ' l) : Γ(M, V)) := by
    intro l V hV
    rcases hl : eN l with _ | ij
    · have hV' : V ≤ ⊥ := by simpa [U', hl] using hV
      exact bijective_smul_of_le_bot M hV' _
    · have h1 : σ' l = mm ij.1 ij.2 := by simp only [σ', hl, Option.elim]
      have h2 : U' l = chartX (f' ij.1) (g ij.1) M (𝔔₀ ij.1) ij.2 := by simp only [U', hl, Option.elim]
      rw [h1]
      rw [h2] at hV
      exact hfr ij.1 ij.2 V hV
  have hU : iSup U' = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨i, hx⟩ := exists_mem_Ug r hr f x
    obtain ⟨y, rfl⟩ := mem_range_p_of (r i) f (f' i) (g i) (hg i) hx
    obtain ⟨j, hj⟩ := exists_mem_chart' (f' i) (g i) M (𝔔₀ i) y
    refine Opens.mem_iSup.mpr ⟨eN.symm (some ⟨i, j⟩), ?_⟩
    rw [hU'some]
    exact ⟨y, hj, rfl⟩

  obtain ⟨𝔓, hσ, -⟩ :=
    Scheme.Modules.exists_projPresentation_of_iSup_eq_top f M N σ' U' hU hframe
  refine ⟨N, 𝔓, fun i => ?_⟩

  obtain ⟨𝔓g, hσg, -, hpb⟩ := Scheme.Modules.ProjPresentation.exists_baseChange_of_isPullback (hg i) 𝔓
  obtain ⟨𝔓', ht', hσ'⟩ := Scheme.Modules.ProjPresentation.exists_of_iso 𝔓g (e i)
  refine ⟨𝔓', by rw [ht']; exact hpb, fun j => ?_⟩
  obtain ⟨c₀, hc₀⟩ := exists_coeff (r i) f (f' i) (g i) (hg i) (nn i j)
  let l₀ : Fin (N + 1) := eN.symm (some ⟨i, j⟩)
  refine ⟨Pi.single l₀ c₀, ?_⟩
  rw [Finset.sum_eq_single l₀]
  · rw [Pi.single_eq_same, hσ', coef_eq]

    have hQ : (𝔔 i).σ j = ((e i).hom.app ⊤) ((𝔔₀ i).σ j) := by
      rw [h𝔔₀σ]
      change (𝔔 i).σ j = (((e i).symm.hom ≫ (e i).hom).app ⊤) ((𝔔 i).σ j)
      rw [Iso.symm_hom, Iso.inv_hom_id, Scheme.Modules.Hom.id_app]
      rfl
    rw [hQ, ← Scheme.Modules.Hom.app_smul]
    congr 1
    rw [hσg, hσ]

    apply map_injective_of_eq _ (preimage_Ug (r i) f (f' i) (g i) (hg i)) (le_top : (g i) ⁻¹ᵁ Ug (r i) f ≤ ⊤)
    have hk : σ' l₀ = mm i j := hσ'some ⟨i, j⟩
    rw [Scheme.Modules.map_smul]
    change _ = _ • ((Scheme.Modules.pullback (g i)).obj M).presheaf.map
      (homOfLE (le_top : (g i) ⁻¹ᵁ Ug (r i) f ≤ ⊤)).op (pull (g i) M ⊤ (σ' l₀))
    rw [hk, (hmm i j), smul_smul]
    have hB : (g i).app (Ug (r i) f) (A.presheaf.map (homOfLE (A.basicOpen_le (gX (r i) f))).op (gX (r i) f ^ nn i j))
        = (A' i).presheaf.map (homOfLE (le_top : (g i) ⁻¹ᵁ Ug (r i) f ≤ ⊤)).op
            ((g i).appTop (gX (r i) f)) ^ nn i j := by
      have := res_app_res (r i) f (g i) (nn i j) (le_rfl : (g i) ⁻¹ᵁ Ug (r i) f ≤ (g i) ⁻¹ᵁ Ug (r i) f)
      rw [show homOfLE (le_rfl : (g i) ⁻¹ᵁ Ug (r i) f ≤ (g i) ⁻¹ᵁ Ug (r i) f) = 𝟙 _ from rfl, op_id,
        CategoryTheory.Functor.map_id] at this
      simpa using this
    rw [hB, ← map_pow, ← map_mul, hc₀, map_one, one_smul]
  · intro l _ hl
    rw [Pi.single_eq_of_ne hl, map_zero, map_zero, zero_smul]
  · intro hl; exact absurd (Finset.mem_univ _) hl

end Main

end AlgebraicGeometry.Scheme.Modules.GlobalPresLocal

end

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_forall_isPullback_toProj_of_forall_away.AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {S : Type u} [CommRing S] {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
    (B : Fin k → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra S (B i)] [∀ i, IsLocalization.Away (r i) (B i)]
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S))
    {A' : Fin k → Scheme.{u}} (f' : ∀ i, A' i ⟶ Spec (CommRingCat.of (B i))) (g : ∀ i, A' i ⟶ A)
    (hg : ∀ i, IsPullback (g i) (f' i) f (Spec.map (CommRingCat.ofHom (algebraMap S (B i)))))
    (hf : IsProper f) (M : A.Modules) (hM : Scheme.Modules.IsInvertible M)
    (M' : ∀ i, (A' i).Modules) (e : ∀ i, (Scheme.Modules.pullback (g i)).obj M ≅ M' i)
    (N' : Fin k → ℕ) (𝔔 : ∀ i, Scheme.Modules.ProjPresentation (M' i) (f' i) (N' i)) :
    ∃ (N : ℕ) (𝔓 : Scheme.Modules.ProjPresentation M f N),
      ∀ i, ∃ 𝔓' : Scheme.Modules.ProjPresentation (M' i) (f' i) N,
        IsPullback (g i) 𝔓'.toProj 𝔓.toProj (ProjSpace.map S (B i) N) ∧
        ∀ j : Fin (N' i + 1), ∃ a : Fin (N + 1) → B i,
          (𝔔 i).σ j = ∑ l, (((f' i).appLE ⊤ ⊤ le_top).hom
            ((Scheme.ΓSpecIso (CommRingCat.of (B i))).inv.hom (a l))) • 𝔓'.σ l :=
  AlgebraicGeometry.Scheme.Modules.GlobalPresLocal.main r hr B f f' g hg hf M hM M' e N' 𝔔

end S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_forall_isPullback_toProj_of_forall_away
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_forall_isPullback_toProj_of_forall_away (solution)
