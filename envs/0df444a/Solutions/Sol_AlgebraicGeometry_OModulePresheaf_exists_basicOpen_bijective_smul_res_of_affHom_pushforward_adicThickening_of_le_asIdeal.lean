-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_basicOpen_bijective_smul_res_of_affHom_pushforward_adicThickening_of_le_asIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/fc52361e-f669-5d0a-a6ec-3a04009a47d5

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_AdicThickening
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isFrameOn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_basicOpen_bijective_smul_res_of_affHom_pushforward_adicThickening_of_le_asIdeal

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

noncomputable section

namespace P2mLBLocal

open AlgebraicGeometry.OModulePresheaf AlgebraicGeometry.Scheme.Modules

section Nakayama

variable {B : Type u} [CommRing B] (𝔭 : Ideal B) [𝔭.IsPrime] (J : Ideal B)
  {N : Type u} [AddCommGroup N] [Module B N]

theorem exists_notMem_forall_smul_mem_span [Module.Finite B N] (hJ : J ≤ 𝔭) (g : N)
    (hA : ∀ m : N, ∃ b : B, m - b • g ∈ J • (⊤ : Submodule B N)) :
    ∃ ρ : B, ρ ∉ 𝔭 ∧ ∀ m : N, ∃ b : B, ρ • m = b • g := by
  let P : Submodule B N := Submodule.span B {g}
  have hle : (⊤ : Submodule B (N ⧸ P)) ≤ J • ⊤ := by
    rintro z -
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective P z
    obtain ⟨b, hb⟩ := hA m
    have h1 : Submodule.Quotient.mk (p := P) m = Submodule.Quotient.mk (m - b • g) := by
      rw [eq_comm, Submodule.Quotient.eq]
      have : m - b • g - m = -(b • g) := by abel
      rw [this]
      exact P.neg_mem (P.smul_mem b (Submodule.subset_span rfl))
    rw [h1]
    have h2 : P.mkQ (m - b • g) ∈ (J • (⊤ : Submodule B N)).map P.mkQ := Submodule.mem_map_of_mem hb
    rw [Submodule.map_smul''] at h2
    exact Submodule.smul_mono le_rfl le_top h2
  obtain ⟨ρ, hρ1, hρ⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul J
    (⊤ : Submodule B (N ⧸ P)) Module.Finite.fg_top hle
  refine ⟨ρ, fun hρp => ?_, fun m => ?_⟩
  · have : (1 : B) ∈ 𝔭 := by
      have h := 𝔭.sub_mem hρp (hJ hρ1)
      rwa [sub_sub_cancel] at h
    exact (inferInstance : 𝔭.IsPrime).ne_top ((Ideal.eq_top_iff_one _).mpr this)
  · have h := hρ (Submodule.Quotient.mk m) Submodule.mem_top
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_span_singleton] at h
    obtain ⟨b, hb⟩ := h
    exact ⟨b, hb.symm⟩

end Nakayama

section Krull

variable {B : Type u} [CommRing B] [IsNoetherianRing B] (𝔭 : Ideal B) [𝔭.IsPrime] (J : Ideal B)

theorem exists_notMem_mul_eq_zero (hJ : J ≤ 𝔭) (b : B)
    (hb : ∀ n : ℕ, ∃ v : B, v ∉ 𝔭 ∧ v * b ∈ J ^ (n + 1)) : ∃ w : B, w ∉ 𝔭 ∧ w * b = 0 := by
  let Bp := Localization.AtPrime 𝔭
  have hJp : J.map (algebraMap B Bp) ≠ ⊤ := by
    intro htop
    have h1 : J.map (algebraMap B Bp) ≤ IsLocalRing.maximalIdeal Bp := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.map_mono hJ
    exact (IsLocalRing.maximalIdeal.isMaximal Bp).ne_top (top_le_iff.mp (htop ▸ h1))
  have hmem : ∀ n : ℕ, algebraMap B Bp b ∈ (J.map (algebraMap B Bp)) ^ n := by
    intro n
    cases n with
    | zero => rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
    | succ n =>
      obtain ⟨v, hv, hvb⟩ := hb n
      have hvu : IsUnit (algebraMap B Bp v) :=
        IsLocalization.map_units Bp (⟨v, hv⟩ : 𝔭.primeCompl)
      have h1 : algebraMap B Bp (v * b) ∈ (J.map (algebraMap B Bp)) ^ (n + 1) := by
        rw [← Ideal.map_pow]
        exact Ideal.mem_map_of_mem _ hvb
      rw [map_mul] at h1
      have h2 := Ideal.mul_mem_left _ (hvu.unit⁻¹ : Bpˣ).1 h1
      rwa [← mul_assoc, IsUnit.val_inv_mul, one_mul] at h2
  have hzero : algebraMap B Bp b = 0 := by
    have h : algebraMap B Bp b ∈ ⨅ n : ℕ, (J.map (algebraMap B Bp)) ^ n := Ideal.mem_iInf.mpr hmem
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ hJp] at h
    exact h
  obtain ⟨⟨w, hw⟩, hwb⟩ := (IsLocalization.map_eq_zero_iff 𝔭.primeCompl Bp b).mp hzero
  exact ⟨w, hw, hwb⟩

theorem exists_notMem_forall_mul_eq_zero (K : Ideal B) (hK : ∀ k ∈ K, ∃ w : B, w ∉ 𝔭 ∧ w * k = 0) :
    ∃ w : B, w ∉ 𝔭 ∧ ∀ k ∈ K, w * k = 0 := by
  classical
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian K : K.FG)
  choose w hw hwk using hK
  let W : B := ∏ k ∈ s.attach, w k.1 (hs ▸ Ideal.subset_span k.2)
  have hW : W ∉ 𝔭 := by
    intro h
    obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    exact hw _ _ hk
  refine ⟨W, hW, ?_⟩
  have hgen : ∀ k ∈ s, W * k = 0 := by
    intro k hk
    have hks : (⟨k, hk⟩ : {x // x ∈ s}) ∈ s.attach := Finset.mem_attach _ _
    obtain ⟨W', hW'⟩ : w k (hs ▸ Ideal.subset_span hk) ∣ W := Finset.dvd_prod_of_mem _ hks
    rw [hW', mul_comm _ W', mul_assoc, hwk, mul_zero]
  intro k hk
  rw [← hs] at hk
  refine Submodule.span_induction (p := fun k _ => W * k = 0) hgen (mul_zero W) ?_ ?_ hk
  · intro a b _ _ ha hb; rw [mul_add, ha, hb, add_zero]
  · intro a b _ hb; rw [smul_eq_mul, mul_left_comm, hb, mul_zero]

end Krull

section Spread

variable {B : Type u} [CommRing B] [IsNoetherianRing B] (𝔭 : Ideal B) [𝔭.IsPrime] (J : Ideal B)
  {N : Type u} [AddCommGroup N] [Module B N]

theorem exists_notMem_ann_and_gen (hJ : J ≤ 𝔭) (g : N)
    (ρ : B) (hρ : ρ ∉ 𝔭) (hρN : ∀ m : N, ∃ b : B, ρ • m = b • g)
    (hB : ∀ (n : ℕ) (b : B), b • g ∈ J ^ (n + 1) • (⊤ : Submodule B N) → ∃ v : B, v ∉ 𝔭 ∧ v * b ∈ J ^ (n + 1)) :
    ∃ r : B, r ∉ 𝔭 ∧ (∀ b : B, b • g = 0 → r * b = 0) ∧ (∀ m : N, ∃ b : B, r • m = b • g) := by
  let K : Ideal B := LinearMap.ker (LinearMap.toSpanSingleton B N g)
  have hK : ∀ k ∈ K, ∃ w : B, w ∉ 𝔭 ∧ w * k = 0 := by
    intro k hk
    have hk0 : k • g = 0 := by
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] at hk
      exact hk
    refine exists_notMem_mul_eq_zero 𝔭 J hJ k fun n => hB n k ?_
    rw [hk0]
    exact Submodule.zero_mem _
  obtain ⟨w, hw, hwK⟩ := exists_notMem_forall_mul_eq_zero 𝔭 K hK
  refine ⟨ρ * w, (inferInstance : 𝔭.IsPrime).mul_notMem hρ hw, fun b hb => ?_, fun m => ?_⟩
  · have : b ∈ K := by
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
      exact hb
    rw [mul_assoc, hwK b this, mul_zero]
  · obtain ⟨b, hb⟩ := hρN m
    refine ⟨w * b, ?_⟩
    rw [mul_comm, mul_smul, hb, ← mul_smul]

end Spread

section PushoutSurj

variable {A B C P : CommRingCat.{u}} {f : A ⟶ C} {q : A ⟶ B} {inl : C ⟶ P} {inr : B ⟶ P}

theorem surjective_and_ker_eq_of_isPushout (h : IsPushout f q inl inr) (hq : Function.Surjective q.hom) :
    Function.Surjective inl.hom ∧ RingHom.ker inl.hom = Ideal.map f.hom (RingHom.ker q.hom) := by
  classical
  set J : Ideal C := Ideal.map f.hom (RingHom.ker q.hom) with hJ
  have hJle : J ≤ RingHom.ker inl.hom := by
    rw [hJ, Ideal.map_le_iff_le_comap]
    intro a ha
    simp only [Ideal.mem_comap, RingHom.mem_ker]
    have hw := congrArg (fun φ : A ⟶ P => φ.hom a) h.w
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at hw
    rw [hw, RingHom.mem_ker.mp ha, map_zero]
  let toQ : C ⟶ CommRingCat.of (C ⧸ J) := CommRingCat.ofHom (Ideal.Quotient.mk J)
  have hker : RingHom.ker q.hom ≤ RingHom.ker ((Ideal.Quotient.mk J).comp f.hom) := by
    intro a ha
    simp only [RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ ha
  let k₀ : B →+* C ⧸ J := RingHom.liftOfSurjective q.hom hq ⟨(Ideal.Quotient.mk J).comp f.hom, hker⟩
  have hk₀ : ∀ a, k₀ (q.hom a) = Ideal.Quotient.mk J (f.hom a) := fun a =>
    RingHom.liftOfRightInverse_comp_apply _ _ _ _ a
  let k : B ⟶ CommRingCat.of (C ⧸ J) := CommRingCat.ofHom k₀
  have w : f ≫ toQ = q ≫ k := by
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, toQ, k, CommRingCat.hom_ofHom]
    exact (hk₀ a).symm
  let d : P ⟶ CommRingCat.of (C ⧸ J) := h.desc toQ k w
  have hd : inl ≫ d = toQ := h.inl_desc toQ k w
  let u₀ : C ⧸ J →+* P := Ideal.Quotient.lift J inl.hom fun c hc => hJle hc
  have hu₀ : ∀ c, u₀ (Ideal.Quotient.mk J c) = inl.hom c := fun c => Ideal.Quotient.lift_mk J _ _
  let u : CommRingCat.of (C ⧸ J) ⟶ P := CommRingCat.ofHom u₀
  have hu : toQ ≫ u = inl := by
    refine CommRingCat.hom_ext (RingHom.ext fun c => ?_)
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, toQ, u, CommRingCat.hom_ofHom]
    exact hu₀ c
  have hdu : d ≫ u = 𝟙 P := by
    apply h.hom_ext
    · rw [← Category.assoc, hd, hu, Category.comp_id]
    · rw [Category.comp_id, ← Category.assoc, h.inr_desc toQ k w]
      refine CommRingCat.hom_ext (RingHom.ext fun b => ?_)
      obtain ⟨a, rfl⟩ := hq b
      simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, k, u, CommRingCat.hom_ofHom]
      rw [hk₀ a, hu₀]
      have hw := congrArg (fun φ : A ⟶ P => φ.hom a) h.w
      simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at hw
      exact hw
  have hud : u ≫ d = 𝟙 _ := by
    refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_id, RingHom.id_apply,
      u, CommRingCat.hom_ofHom]
    rw [hu₀]
    have := congrArg (fun φ : C ⟶ _ => φ.hom c) hd
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, toQ, CommRingCat.hom_ofHom] at this
    exact this
  have hu_surj : Function.Surjective u.hom := by
    intro p
    refine ⟨d.hom p, ?_⟩
    have := congrArg (fun φ : P ⟶ P => φ.hom p) hdu
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_id, RingHom.id_apply] at this
    exact this
  have hu_inj : Function.Injective u.hom := by
    intro x y hxy
    have hx := congrArg (fun φ : CommRingCat.of (C ⧸ J) ⟶ _ => φ.hom x) hud
    have hy := congrArg (fun φ : CommRingCat.of (C ⧸ J) ⟶ _ => φ.hom y) hud
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_id, RingHom.id_apply] at hx hy
    rw [← hx, ← hy, hxy]
  have hinl : ∀ c, inl.hom c = u.hom (Ideal.Quotient.mk J c) := fun c => (hu₀ c).symm
  refine ⟨?_, ?_⟩
  · intro p
    obtain ⟨x, hx⟩ := hu_surj p
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨c, (hinl c).trans hx⟩
  · ext c
    rw [RingHom.mem_ker, hinl, ← Ideal.Quotient.eq_zero_iff_mem]
    constructor
    · intro hc
      exact hu_inj (hc.trans (map_zero u.hom).symm)
    · intro hc
      rw [hc, map_zero]

end PushoutSurj

section RingCat

variable {X Y Z : CommRingCat.{u}}

theorem surj_hom_of_isIso (a : X ⟶ Y) [IsIso a] : Function.Surjective a.hom := fun y =>
  ⟨(inv a).hom y, by rw [← CommRingCat.comp_apply, IsIso.inv_hom_id]; rfl⟩

theorem inj_hom_of_isIso (a : X ⟶ Y) [IsIso a] : Function.Injective a.hom := fun x x' h => by
  have := congrArg (inv a).hom h
  rwa [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, IsIso.hom_inv_id] at this

theorem ker_comp_of_injective (b : X ⟶ Y) (c : Y ⟶ Z) (hc : Function.Injective c.hom) :
    RingHom.ker (b ≫ c).hom = RingHom.ker b.hom := by
  ext x
  rw [RingHom.mem_ker, RingHom.mem_ker, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  constructor
  · intro h
    exact hc (h.trans (map_zero c.hom).symm)
  · intro h
    rw [h, map_zero]

theorem ker_comp_eq_comap (a : X ⟶ Y) (b : Y ⟶ Z) :
    RingHom.ker (a ≫ b).hom = (RingHom.ker b.hom).comap a.hom := by
  ext x
  rw [RingHom.mem_ker, Ideal.mem_comap, RingHom.mem_ker, CommRingCat.hom_comp, RingHom.coe_comp,
    Function.comp_apply]

theorem surjective_comp_iff_of_isIso_right (b : X ⟶ Y) (c : Y ⟶ Z) [IsIso c] :
    Function.Surjective (b ≫ c).hom ↔ Function.Surjective b.hom := by
  rw [CommRingCat.hom_comp, RingHom.coe_comp]
  constructor
  · intro h y
    obtain ⟨x, hx⟩ := h (c.hom y)
    exact ⟨x, inj_hom_of_isIso c hx⟩
  · intro h
    exact (surj_hom_of_isIso c).comp h

theorem surjective_comp_iff_of_isIso_left (a : X ⟶ Y) (b : Y ⟶ Z) [IsIso a] :
    Function.Surjective (a ≫ b).hom ↔ Function.Surjective b.hom := by
  rw [CommRingCat.hom_comp, RingHom.coe_comp]
  constructor
  · intro h
    exact Function.Surjective.of_comp h
  · intro h
    exact h.comp (surj_hom_of_isIso a)

theorem comap_hom_eq_map_inv (e : X ≅ Y) (K : Ideal Y) : K.comap e.hom.hom = K.map e.inv.hom := by
  apply le_antisymm
  · intro x hx
    have hx' : x = e.inv.hom (e.hom.hom x) := by rw [← CommRingCat.comp_apply, e.hom_inv_id]; rfl
    rw [hx']
    exact Ideal.mem_map_of_mem _ hx
  · rw [Ideal.map_le_iff_le_comap]
    intro z hz
    rw [Ideal.mem_comap, Ideal.mem_comap, ← CommRingCat.comp_apply, e.inv_hom_id]
    exact hz

theorem map_hom_comap_hom (e : X ≅ Y) (K : Ideal Y) : (K.comap e.hom.hom).map e.hom.hom = K :=
  Ideal.map_comap_of_surjective _ (surj_hom_of_isIso e.hom) K

theorem map_hom_map_inv (e : X ≅ Y) (K : Ideal Y) : (K.map e.inv.hom).map e.hom.hom = K := by
  rw [Ideal.map_map, ← CommRingCat.hom_comp, e.inv_hom_id, CommRingCat.hom_id, Ideal.map_id]

end RingCat

section Kernel

variable {Z₀ Z₁ : Scheme.{u}} (y : Z₀ ⟶ Z₁)
  {A' A : Type u} [CommRing A'] [CommRing A] (φ : A' →+* A) (hφ : Function.Surjective φ)
  (p₁ : Z₁ ⟶ Spec (.of A')) (p₀ : Z₀ ⟶ Spec (.of A))
  (H : IsPullback y p₀ p₁ (Spec.map (CommRingCat.ofHom φ)))

theorem appLE_congr_hom {X Y : Scheme.{u}} {k k' : X ⟶ Y} (e : k = k') (U : Y.Opens) (W : X.Opens)
    (h : W ≤ k ⁻¹ᵁ U) (h' : W ≤ k' ⁻¹ᵁ U) : k.appLE U W h = k'.appLE U W h' := by
  subst e; rfl

theorem appTop_SpecMap :
    (Spec.map (CommRingCat.ofHom φ)).appTop =
      (Scheme.ΓSpecIso (.of A')).hom ≫ CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (.of A)).inv := by
  rw [← Category.assoc, ← Scheme.ΓSpecIso_naturality, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem appLE_top_top {S T : Scheme.{u}} (t : T ⟶ S) : t.appLE ⊤ ⊤ le_top = t.appTop := by
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

include hφ H in

theorem surjective_and_ker_appLE_core (W₁ : Z₁.Opens) (hW₁ : IsAffineOpen W₁) :
    Function.Surjective (y.appLE W₁ (y ⁻¹ᵁ W₁ ⊓ p₀ ⁻¹ᵁ ⊤) (by simp)) ∧
      RingHom.ker (y.appLE W₁ (y ⁻¹ᵁ W₁ ⊓ p₀ ⁻¹ᵁ ⊤) (by simp)).hom =
        ((RingHom.ker φ).map (Scheme.ΓSpecIso (.of A')).inv.hom).map (p₁.appLE ⊤ W₁ le_top).hom := by
  set UY : Z₀.Opens := y ⁻¹ᵁ W₁ ⊓ p₀ ⁻¹ᵁ ⊤ with hUY
  have Hres := Scheme.Hom.isPullback_resLE H (US := ⊤) (UT := ⊤) (UX := W₁) le_top le_top (UY := UY) hUY
  haveI : IsAffine W₁ := hW₁
  haveI : IsAffine (⊤ : (Spec (CommRingCat.of A')).Opens) := isAffineOpen_top _
  haveI : IsAffine (⊤ : (Spec (CommRingCat.of A)).Opens) := isAffineOpen_top _
  have hpo := isPushout_appTop_of_isPullback Hres
  have hg' : Function.Surjective ((Spec.map (CommRingCat.ofHom φ)).resLE ⊤ ⊤ le_top).appTop.hom := by
    rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, appLE_top_top, appTop_SpecMap,
      surjective_comp_iff_of_isIso_left, surjective_comp_iff_of_isIso_right, surjective_comp_iff_of_isIso_left,
      surjective_comp_iff_of_isIso_right]
    exact hφ
  obtain ⟨hsurj, hker⟩ := surjective_and_ker_eq_of_isPushout hpo hg'
  rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top] at hsurj hker
  rw [surjective_comp_iff_of_isIso_left, surjective_comp_iff_of_isIso_right] at hsurj
  refine ⟨hsurj, ?_⟩
  rw [ker_comp_eq_comap, ker_comp_of_injective _ _ (inj_hom_of_isIso _)] at hker
  have hker' := congrArg (Ideal.map (W₁.topIso.hom.hom)) hker
  rw [map_hom_comap_hom] at hker'
  rw [hker']
  rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, appLE_top_top,
    appTop_SpecMap]
  rw [ker_comp_eq_comap, ker_comp_of_injective _ _ (inj_hom_of_isIso _), ker_comp_eq_comap,
    ker_comp_of_injective _ _ (inj_hom_of_isIso _), CommRingCat.hom_ofHom]
  rw [CommRingCat.hom_comp, CommRingCat.hom_comp, ← Ideal.map_map, ← Ideal.map_map]
  rw [map_hom_comap_hom, comap_hom_eq_map_inv, map_hom_map_inv]

theorem preimage_eq_inf' (W₁ : Z₁.Opens) : y ⁻¹ᵁ W₁ = y ⁻¹ᵁ W₁ ⊓ p₀ ⁻¹ᵁ ⊤ := by
  ext1
  simp

theorem app_eq_comp (W₁ : Z₁.Opens) :
    y.app W₁ = y.appLE W₁ (y ⁻¹ᵁ W₁ ⊓ p₀ ⁻¹ᵁ ⊤) (by simp) ≫
        Z₀.presheaf.map (eqToHom (preimage_eq_inf' y p₀ W₁)).op := by
  rw [Scheme.Hom.app_eq_appLE]
  exact (Scheme.Hom.appLE_map' y _ _).symm

end Kernel

section Thick

variable {R : Type u} [CommRing R] (I : Ideal R) {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

abbrev rf {A C : X.Opens} (h : C ≤ A) : Γ(X, A) →+* Γ(X, C) := (X.presheaf.map (homOfLE h).op).hom

theorem rf_rf {A C D : X.Opens} (hCA : C ≤ A) (hDC : D ≤ C) (a : Γ(X, A)) : rf hDC (rf hCA a) = rf (hDC.trans hCA) a := by
  change (X.presheaf.map (homOfLE hCA).op ≫ X.presheaf.map (homOfLE hDC).op).hom a = _
  rw [← Functor.map_comp]; rfl

abbrev algR (W : X.Opens) : R →+* Γ(X, W) := ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appLE ⊤ W le_top).hom

theorem rf_algR {A C : X.Opens} (h : C ≤ A) (r : R) : rf h (algR f A r) = algR f C r := by
  change (((Scheme.ΓSpecIso (.of R)).inv ≫ f.appLE ⊤ A le_top) ≫ X.presheaf.map (homOfLE h).op).hom r = _
  rw [Category.assoc, Scheme.Hom.appLE_map]

theorem map_algR {A C : X.Opens} (h : C ≤ A) (K : Ideal R) : (K.map (algR f A)).map (rf h) = K.map (algR f C) := by
  rw [Ideal.map_map]
  congr 1
  exact RingHom.ext fun r => rf_algR f h r

theorem isPullback_thick (n : ℕ) :
    IsPullback (adicThickeningι f I n) (adicThickeningToBase f I n) f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))) :=
  IsPullback.of_hasPullback f (adicThickeningBase I n)

theorem ringFacts (n : ℕ) (W : X.affineOpens) :
    Function.Surjective ((adicThickeningι f I n).app W.1).hom ∧
      RingHom.ker ((adicThickeningι f I n).app W.1).hom = (I ^ (n + 1)).map (algR f W.1) := by
  obtain ⟨hs, hk⟩ := surjective_and_ker_appLE_core (adicThickeningι f I n) (Ideal.Quotient.mk (I ^ (n + 1)))
    Ideal.Quotient.mk_surjective f (adicThickeningToBase f I n) (isPullback_thick I f n) W.1 W.2
  rw [app_eq_comp (adicThickeningι f I n) (adicThickeningToBase f I n) W.1]
  refine ⟨(surjective_comp_iff_of_isIso_right _ _).mpr hs, ?_⟩
  rw [ker_comp_of_injective _ _ (inj_hom_of_isIso _), hk, Ideal.mk_ker, Ideal.map_map]
  rfl

theorem exists_pt (n : ℕ) (x : X) (hx : I ≤ (f.base x).asIdeal) :
    ∃ xn : adicThickening f I n, (adicThickeningι f I n).base xn = x := by
  have hmem : f.base x ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (I ^ (n + 1)))) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    change ((I ^ (n + 1) : Ideal R) : Set R) ⊆ ((f.base x).asIdeal : Set R)
    exact fun r hr => hx (Ideal.pow_le_self (Nat.succ_ne_zero n) hr)
  obtain ⟨y, hy⟩ := hmem
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := adicThickeningBase I n) x y
    (by rw [← hy]; rfl)
  exact ⟨z, hz⟩

variable (L : ∀ n : ℕ, (adicThickening f I n).Modules) (hL : ∀ n, Scheme.Modules.IsInvertible (L n))

include hL in

theorem exists_frame (n : ℕ) (V : X.affineOpens) (x : X) (hxV : x ∈ V.1) (hx : I ≤ (f.base x).asIdeal) :
    ∃ (s : Γ(X, V.1)) (t : Γ(L n, adicThickeningι f I n ⁻¹ᵁ X.basicOpen s)),
      x ∈ X.basicOpen s ∧ IsFrameOn t (adicThickeningι f I n ⁻¹ᵁ X.basicOpen s) := by
  set ι := adicThickeningι f I n with hι
  obtain ⟨xn, hxn⟩ := exists_pt I f n x hx
  obtain ⟨W, t, hxW, ht⟩ := Scheme.Modules.IsInvertible.exists_isFrameOn (hL n) xn
  obtain ⟨O, hO, hOW⟩ := ι.isClosedEmbedding.isInducing.isOpen_iff.mp W.2
  have hxO : x ∈ O := by
    have : xn ∈ ι.base ⁻¹' O := by rw [hOW]; exact hxW
    rw [← hxn]; exact this
  obtain ⟨s, hsO, hxs⟩ := V.2.exists_basicOpen_le (V := ⟨O, hO⟩) ⟨x, hxO⟩ hxV
  have hle : ι ⁻¹ᵁ X.basicOpen s ≤ W := by
    intro z hz
    have hz' : ι.base z ∈ O := hsO hz
    have : z ∈ ι.base ⁻¹' O := hz'
    rw [hOW] at this
    exact this
  exact ⟨s, (L n).presheaf.map (homOfLE hle).op t, hxs, (ht.map (homOfLE hle)).mono hle⟩

end Thick

section Read

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (G : OModulePresheaf f)
  {X' : Scheme.{u}} (ι : X' ⟶ X) (L : X'.Modules)
  (ψ : OModulePresheaf.AffHom G (OModulePresheaf.pushforward f ι (OModulePresheaf.ofModules (ι ≫ f) L)))

def toL (V : X.Opens) (m : (OModulePresheaf.pushforward f ι (OModulePresheaf.ofModules (ι ≫ f) L)).obj V) :
    Γ(L, ι ⁻¹ᵁ V) := m

theorem toL_zero (V : X.Opens) : toL f ι L V 0 = 0 := rfl

theorem toL_injective (V : X.Opens) : Function.Injective (toL f ι L V) := fun _ _ h => h

theorem psi_smul (V : X.affineOpens) (a : Γ(X, V.1)) (x : G.obj V.1) :
    toL f ι L V.1 (ψ.app V (a • x)) = ι.app V.1 a • toL f ι L V.1 (ψ.app V x) := by
  rw [ψ.app_smul V a x, ← Scheme.Hom.appLE_eq_app]
  rfl

theorem psi_res {V V' : X.affineOpens} (h : V.1 ≤ V'.1) (x : G.obj V'.1) :
    toL f ι L V.1 (ψ.app V (G.res h x)) =
      L.presheaf.map (homOfLE ((Opens.map ι.base).monotone h)).op (toL f ι L V'.1 (ψ.app V' x)) :=
  ψ.naturality_apply h x

theorem frame_self {W : X'.Opens} {t : Γ(L, W)} (ht : IsFrameOn t W) :
    Function.Bijective fun c : Γ(X', W) => c • t := by
  have e : L.presheaf.map (homOfLE (le_refl W)).op t = t := by
    rw [Subsingleton.elim (homOfLE (le_refl W)) (𝟙 W), op_id, L.presheaf.map_id]; rfl
  have h := ht le_rfl le_rfl
  rw [e] at h
  exact h

end Read

section Core

variable {R : Type u} [CommRing R] (I : Ideal R)
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
  (L : ∀ n : ℕ, (adicThickening f I n).Modules)
  (hL : ∀ n, Scheme.Modules.IsInvertible (L n))
  (G : OModulePresheaf f) (hGc : G.IsCoherent) (hGq : G.IsQuasicoherent)
  (ψ : ∀ n : ℕ, OModulePresheaf.AffHom G
      (OModulePresheaf.pushforward f (adicThickeningι f I n)
        (OModulePresheaf.ofModules (adicThickeningι f I n ≫ f) (L n))))
  (hψs : ∀ (n : ℕ) (U : X.affineOpens), Function.Surjective ((ψ n).app U))
  (hψk : ∀ (n : ℕ) (U : X.affineOpens),
    LinearMap.ker ((ψ n).app U) = I ^ (n + 1) • (⊤ : Submodule R (G.obj U.1)))
  (V : X.affineOpens) (x : X) (hxV : x ∈ V.1) (hx : I ≤ (f.base x).asIdeal)

abbrev JJ : Ideal Γ(X, V.1) := I.map (algR f V.1)

def pp : Ideal Γ(X, V.1) :=
  (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).comap (X.presheaf.germ V.1 x hxV).hom

scoped instance pp_isPrime : (pp V x hxV).IsPrime := by
  unfold pp; infer_instance

theorem mem_pp (s : Γ(X, V.1)) : s ∈ pp V x hxV ↔ x ∉ X.basicOpen s := by
  rw [pp, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Scheme.mem_basicOpen]

include hx in
theorem JJ_le_pp : JJ I f V ≤ pp V x hxV := by
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  rw [Ideal.mem_comap, mem_pp]
  intro hxr
  change x ∈ X.basicOpen (f.appLE ⊤ V.1 le_top ((Scheme.ΓSpecIso (.of R)).inv r)) at hxr
  rw [Scheme.basicOpen_appLE, basicOpen_eq_of_affine] at hxr
  exact (PrimeSpectrum.mem_basicOpen _ _).mp hxr.2 (hx hr)

include hψk in

theorem mem_pow_smul_iff (n : ℕ) (y : G.obj V.1) :
    y ∈ JJ I f V ^ (n + 1) • (⊤ : Submodule Γ(X, V.1) (G.obj V.1)) ↔ (ψ n).app V y = 0 := by
  letI : Algebra R Γ(X, V.1) := Scheme.TwoAffineOpenCover.algebraOfHom f V.1
  haveI : IsScalarTower R Γ(X, V.1) (G.obj V.1) := G.isScalarTower V.1
  have key : (JJ I f V ^ (n + 1) • (⊤ : Submodule Γ(X, V.1) (G.obj V.1))).restrictScalars R =
      I ^ (n + 1) • (⊤ : Submodule R (G.obj V.1)) := by
    rw [JJ, show algR f V.1 = algebraMap R Γ(X, V.1) from rfl, ← Ideal.map_pow, Ideal.smul_restrictScalars,
      Submodule.restrictScalars_top]
  rw [← LinearMap.mem_ker, hψk n V, ← key]
  exact Iff.rfl

section WithFrame

variable (t : Γ(L 0, adicThickeningι f I 0 ⁻¹ᵁ V.1)) (ht : IsFrameOn t (adicThickeningι f I 0 ⁻¹ᵁ V.1))

def gen : G.obj V.1 := (hψs 0 V t).choose

theorem gen_spec : toL f (adicThickeningι f I 0) (L 0) V.1 ((ψ 0).app V (gen I f L G ψ hψs V t)) = t :=
  (hψs 0 V t).choose_spec

include ht hψk in

theorem hA (m : G.obj V.1) : ∃ b : Γ(X, V.1),
    m - b • gen I f L G ψ hψs V t ∈ JJ I f V • (⊤ : Submodule Γ(X, V.1) (G.obj V.1)) := by
  set ι := adicThickeningι f I 0 with hι
  obtain ⟨c, hc⟩ := (frame_self (L 0) ht).2 (toL f ι (L 0) V.1 ((ψ 0).app V m))
  obtain ⟨b, hb⟩ := (ringFacts I f 0 V).1 c
  refine ⟨b, ?_⟩
  rw [← pow_one (JJ I f V), mem_pow_smul_iff I f L G ψ hψk, map_sub, sub_eq_zero]
  apply toL_injective f ι (L 0) V.1
  rw [psi_smul, gen_spec, ← hc, ← hb]

include hψk hGq hx hL in

theorem hB (ρ : Γ(X, V.1)) (hρ : ρ ∉ pp V x hxV)
    (hρN : ∀ m : G.obj V.1, ∃ b : Γ(X, V.1), ρ • m = b • gen I f L G ψ hψs V t)
    (n : ℕ) (b : Γ(X, V.1))
    (hb : b • gen I f L G ψ hψs V t ∈ JJ I f V ^ (n + 1) • (⊤ : Submodule Γ(X, V.1) (G.obj V.1))) :
    ∃ v : Γ(X, V.1), v ∉ pp V x hxV ∧ v * b ∈ JJ I f V ^ (n + 1) := by
  set g₀ := gen I f L G ψ hψs V t with hg₀
  set ι := adicThickeningι f I n with hι

  have h0 : (ψ n).app V (b • g₀) = 0 := (mem_pow_smul_iff I f L G ψ hψk V n _).mp hb

  obtain ⟨s, tn, hxs, htn⟩ := exists_frame I f L hL n V x hxV hx
  let D : X.affineOpens := ⟨X.basicOpen s, V.2.basicOpen s⟩
  have hD : D.1 ≤ V.1 := X.basicOpen_le s

  let φ : Γ(X, D.1) →+* Γ(adicThickening f I n, ι ⁻¹ᵁ D.1) := (ι.app D.1).hom
  have hφ : ∀ a : Γ(X, D.1), ι.app D.1 a = φ a := fun a => rfl

  have h3 : φ (rf hD b) • toL f ι (L n) D.1 ((ψ n).app D (G.res hD g₀)) = 0 := by
    have h := psi_res f G ι (L n) (ψ n) (V := D) (V' := V) hD (b • g₀)
    rw [h0, toL_zero, map_zero, G.res_smul, psi_smul] at h
    exact h

  obtain ⟨c, hc⟩ := (frame_self (L n) htn).2 (toL f ι (L n) D.1 ((ψ n).app D (G.res hD g₀)))
  dsimp only at hc

  obtain ⟨m', hm'⟩ := hψs n D tn
  obtain ⟨k, m, hm⟩ := (hGq V s).1 m'
  obtain ⟨b₀, hb₀⟩ := hρN m

  have h6 : φ (rf hD (ρ * s ^ k)) = φ (rf hD b₀) * c := by
    apply (frame_self (L n) htn).1
    change (φ (rf hD (ρ * s ^ k))) • tn = (φ (rf hD b₀) * c) • tn
    have hA1 : toL f ι (L n) D.1 ((ψ n).app D (G.res hD (ρ • m))) = (φ (rf hD (ρ * s ^ k))) • tn := by
      rw [G.res_smul, psi_smul, hm, psi_smul, hφ, hφ, ← mul_smul, ← map_mul, ← map_mul]
      exact congrArg _ hm'
    have hA2 : toL f ι (L n) D.1 ((ψ n).app D (G.res hD (ρ • m))) = (φ (rf hD b₀) * c) • tn := by
      rw [hb₀, G.res_smul, psi_smul, hφ, ← hc, mul_smul]
    rw [← hA1, hA2]

  have h7 : φ (rf hD b) * c = 0 := by
    apply (frame_self (L n) htn).1
    change (φ (rf hD b) * c) • tn = (0 : Γ(adicThickening f I n, ι ⁻¹ᵁ D.1)) • tn
    rw [mul_smul, hc, zero_smul]
    exact h3

  have h8 : rf hD (b * (ρ * s ^ k)) ∈ (JJ I f V ^ (n + 1)).map (rf hD) := by
    rw [JJ, ← Ideal.map_pow, map_algR f hD, ← (ringFacts I f n D).2, RingHom.mem_ker]
    change φ (rf hD (b * (ρ * s ^ k))) = 0
    rw [map_mul, map_mul, h6, mul_left_comm, h7, mul_zero]

  haveI := V.2.isLocalization_basicOpen s
  have halg : ∀ a : Γ(X, V.1), algebraMap Γ(X, V.1) Γ(X, X.basicOpen s) a = rf hD a := fun a => rfl
  obtain ⟨⟨⟨i₀, hi₀⟩, ⟨_, ⟨j, rfl⟩⟩⟩, hij⟩ :=
    (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers s) Γ(X, X.basicOpen s)).mp h8
  simp only at hij
  rw [halg, halg, ← map_mul, ← sub_eq_zero, ← map_sub, ← halg,
    IsLocalization.map_eq_zero_iff (Submonoid.powers s)] at hij
  obtain ⟨⟨_, ⟨l, rfl⟩⟩, hl⟩ := hij
  simp only at hl
  refine ⟨s ^ l * (ρ * s ^ k) * s ^ j, ?_, ?_⟩
  · have hs : s ∉ pp V x hxV := by rw [mem_pp, not_not]; exact hxs
    have hsub : ∀ a b : Γ(X, V.1), a ∉ pp V x hxV → b ∉ pp V x hxV → a * b ∉ pp V x hxV :=
      fun a b ha hb => (inferInstance : (pp V x hxV).IsPrime).mul_notMem ha hb
    have hpow : ∀ (a : Γ(X, V.1)) (e : ℕ), a ∉ pp V x hxV → a ^ e ∉ pp V x hxV := fun a e ha h =>
      ha ((inferInstance : (pp V x hxV).IsPrime).mem_of_pow_mem e h)
    exact hsub _ _ (hsub _ _ (hpow s l hs) (hsub _ _ hρ (hpow s k hs))) (hpow s j hs)
  · rw [mul_sub, sub_eq_zero] at hl
    have : s ^ l * (ρ * s ^ k) * s ^ j * b = s ^ l * (b * (ρ * s ^ k) * s ^ j) := by ring
    rw [this, hl]
    exact Ideal.mul_mem_left _ _ hi₀

include ht hψs hψk hGq hGc hxV hx hL in

theorem core [IsNoetherianRing R] [LocallyOfFiniteType f] : ∃ (r : Γ(X, V.1)) (g : G.obj V.1), x ∈ X.basicOpen r ∧
    Function.Bijective fun b : Γ(X, X.basicOpen r) => b • G.res (X.basicOpen_le r) g := by
  set g₀ := gen I f L G ψ hψs V t with hg₀

  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : IsNoetherianRing Γ(X, V.1) := IsLocallyNoetherian.component_noetherian V
  haveI : Module.Finite Γ(X, V.1) (G.obj V.1) := hGc V

  obtain ⟨ρ, hρ, hρN⟩ := P2mLBLocal.exists_notMem_forall_smul_mem_span (pp V x hxV) (JJ I f V)
    (JJ_le_pp I f V x hxV hx) g₀ (hA I f L G ψ hψs hψk V t ht)

  obtain ⟨r, hr, hann, hgen⟩ := P2mLBLocal.exists_notMem_ann_and_gen (pp V x hxV) (JJ I f V)
    (JJ_le_pp I f V x hxV hx) g₀ ρ hρ hρN (hB I f L hL G hGq ψ hψs hψk V x hxV hx t ρ hρ hρN)
  have hxr : x ∈ X.basicOpen r := by rw [mem_pp, not_not] at hr; exact hr
  refine ⟨r, g₀, hxr, ?_⟩

  haveI := V.2.isLocalization_basicOpen r
  have hDr : X.basicOpen r ≤ V.1 := X.basicOpen_le r
  have halg : ∀ a : Γ(X, V.1), algebraMap Γ(X, V.1) Γ(X, X.basicOpen r) a = rf hDr a := fun a => rfl
  have hu : ∀ e : ℕ, IsUnit (rf hDr (r ^ e)) := fun e => by
    rw [← halg, map_pow]; exact (IsLocalization.Away.algebraMap_isUnit r).pow e
  set E : G.obj (X.basicOpen r) := G.res hDr g₀ with hE

  have hinj0 : ∀ b' : Γ(X, X.basicOpen r), b' • E = 0 → b' = 0 := by
    intro b' hb'
    obtain ⟨⟨b, ⟨_, ⟨k, rfl⟩⟩⟩, hbk⟩ := IsLocalization.surj (Submonoid.powers r) b'
    simp only at hbk
    rw [halg, halg] at hbk
    have h1 : G.res hDr (b • g₀) = 0 := by
      rw [G.res_smul, ← hbk, mul_comm, mul_smul]
      change rf hDr (r ^ k) • (b' • E) = 0
      rw [hb', smul_zero]
    obtain ⟨c, hc⟩ := (hGq V r).2 _ h1
    rw [← mul_smul] at hc
    have h2 : r ^ (c + 1) * b = 0 := by rw [pow_succ', mul_assoc]; exact hann _ hc
    have h3 : rf hDr b = 0 := by
      have := congrArg (rf hDr) h2
      rw [map_mul, map_zero] at this
      exact ((hu (c + 1)).mul_right_eq_zero).mp this
    rw [h3] at hbk
    exact ((hu k).mul_left_eq_zero).mp hbk
  constructor
  · intro b₁ b₂ h
    have : (b₁ - b₂) • E = 0 := by
      change (b₁ - b₂) • E = 0
      rw [sub_smul]
      exact sub_eq_zero.mpr h
    exact sub_eq_zero.mp (hinj0 _ this)
  · intro y
    obtain ⟨k, m, hm⟩ := (hGq V r).1 y
    obtain ⟨b, hb⟩ := hgen m
    have h1 : rf hDr (r ^ (k + 1)) • y = rf hDr b • E := by
      rw [pow_succ', map_mul, mul_smul]
      change rf hDr r • ((X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom (r ^ k) • y) = _
      rw [← hm, ← G.res_smul, hb, G.res_smul]
    refine ⟨((hu (k + 1)).unit⁻¹ : Γ(X, X.basicOpen r)ˣ).1 * rf hDr b, ?_⟩
    change (((hu (k + 1)).unit⁻¹ : Γ(X, X.basicOpen r)ˣ).1 * rf hDr b) • E = y
    rw [mul_smul, ← h1, ← mul_smul, IsUnit.val_inv_mul, one_smul]

end WithFrame

end Core

section Main

variable {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f]
  (L : ∀ n : ℕ, (adicThickening f I n).Modules)
  (hL : ∀ n, Scheme.Modules.IsInvertible (L n))
  (G : OModulePresheaf f) (hGc : G.IsCoherent) (hGq : G.IsQuasicoherent)
  (ψ : ∀ n : ℕ, OModulePresheaf.AffHom G
      (OModulePresheaf.pushforward f (adicThickeningι f I n)
        (OModulePresheaf.ofModules (adicThickeningι f I n ≫ f) (L n))))
  (hψs : ∀ (n : ℕ) (U : X.affineOpens), Function.Surjective ((ψ n).app U))
  (hψk : ∀ (n : ℕ) (U : X.affineOpens),
    LinearMap.ker ((ψ n).app U) = I ^ (n + 1) • (⊤ : Submodule R (G.obj U.1)))

omit [IsNoetherianRing R] [LocallyOfFiniteType f] in

theorem transport {A W W' : X.Opens} (e : W = W') (h : W ≤ A) (h' : W' ≤ A) (m : G.obj A)
    (hb : Function.Bijective fun b : Γ(X, W) => b • G.res h m) :
    Function.Bijective fun b : Γ(X, W') => b • G.res h' m := by
  subst e
  exact hb

omit [IsNoetherianRing R] [LocallyOfFiniteType f] in

theorem bijective_smul_unit_smul {W : X.Opens} (m : G.obj W) (u : Γ(X, W)) (hu : IsUnit u)
    (hb : Function.Bijective fun b : Γ(X, W) => b • m) :
    Function.Bijective fun b : Γ(X, W) => b • (u • m) := by
  have : (fun b : Γ(X, W) => b • (u • m)) = (fun b : Γ(X, W) => b • m) ∘ fun b => b * u := by
    funext b; simp only [Function.comp_apply, mul_smul]
  rw [this]
  exact hb.comp ((IsUnit.isUnit_iff_mulRight_bijective (a := u)).mp hu)

include hL hGc hGq hψs hψk in
theorem main (U : X.affineOpens) (x : X) (hxU : x ∈ U.1) (hx : I ≤ (f.base x).asIdeal) :
    ∃ (r : Γ(X, U.1)) (g : G.obj U.1), x ∈ X.basicOpen r ∧
      Function.Bijective fun b : Γ(X, X.basicOpen r) => b • G.res (X.basicOpen_le r) g := by

  obtain ⟨s, t, hxs, ht⟩ := exists_frame I f L hL 0 U x hxU hx
  let V : X.affineOpens := ⟨X.basicOpen s, U.2.basicOpen s⟩
  have hV : V.1 ≤ U.1 := X.basicOpen_le s
  obtain ⟨r₁, g₁, hxr₁, hbij⟩ := core I f L hL G hGc hGq ψ hψs hψk V x hxs hx t ht

  haveI := U.2.isLocalization_basicOpen s
  have halg : ∀ a : Γ(X, U.1), algebraMap Γ(X, U.1) Γ(X, X.basicOpen s) a = rf hV a := fun a => rfl
  obtain ⟨⟨a, ⟨_, ⟨j, rfl⟩⟩⟩, haj⟩ := IsLocalization.surj (Submonoid.powers s) r₁
  simp only at haj
  rw [halg, halg] at haj
  obtain ⟨k, g, hg⟩ := (hGq U s).1 g₁
  have hus : ∀ e : ℕ, IsUnit (rf hV (s ^ e)) := fun e => by
    rw [← halg, map_pow]; exact (IsLocalization.Away.algebraMap_isUnit s).pow e

  have heq : X.basicOpen r₁ = X.basicOpen (a * s) := by
    have h1 : X.basicOpen (r₁ * rf hV (s ^ j)) = X.basicOpen r₁ := by
      rw [Scheme.basicOpen_mul, X.basicOpen_of_isUnit (hus j)]
      exact inf_eq_left.mpr (X.basicOpen_le r₁)
    have h2 : X.basicOpen (rf hV a) = X.basicOpen (a * s) := by
      change X.basicOpen (X.presheaf.map (homOfLE hV).op a) = _
      rw [Scheme.basicOpen_res, Scheme.basicOpen_mul, inf_comm]
    rw [← h1, haj, h2]
  refine ⟨a * s, g, heq ▸ hxr₁, ?_⟩
  have hle₁ : X.basicOpen r₁ ≤ V.1 := X.basicOpen_le r₁
  have hle : X.basicOpen (a * s) ≤ V.1 := heq ▸ hle₁

  have hb1 : Function.Bijective fun b : Γ(X, X.basicOpen (a * s)) => b • G.res hle g₁ :=
    transport f G heq hle₁ hle g₁ hbij
  have hres : G.res (X.basicOpen_le (a * s)) g = rf hle (rf hV (s ^ k)) • G.res hle g₁ := by
    rw [← G.res_res hle hV, hg, G.res_smul]
  have hb2 := bijective_smul_unit_smul f G (G.res hle g₁) (rf hle (rf hV (s ^ k))) ((hus k).map _) hb1
  rw [← hres] at hb2
  exact hb2

end Main

end P2mLBLocal
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_basicOpen_bijective_smul_res_of_affHom_pushforward_adicThickening_of_le_asIdeal.P2mLBLocal"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_basicOpen_bijective_smul_res_of_affHom_pushforward_adicThickening_of_le_asIdeal.P2mLBLocal"

theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f]
    (L : ∀ n : ℕ, (adicThickening f I n).Modules)
    (hL : ∀ n, Scheme.Modules.IsInvertible (L n))
    (G : OModulePresheaf f) (hGc : G.IsCoherent) (hGq : G.IsQuasicoherent)
    (ψ : ∀ n : ℕ, OModulePresheaf.AffHom G
        (OModulePresheaf.pushforward f (adicThickeningι f I n)
          (OModulePresheaf.ofModules (adicThickeningι f I n ≫ f) (L n))))
    (hψs : ∀ (n : ℕ) (U : X.affineOpens), Function.Surjective ((ψ n).app U))
    (hψk : ∀ (n : ℕ) (U : X.affineOpens),
      LinearMap.ker ((ψ n).app U) = I ^ (n + 1) • (⊤ : Submodule R (G.obj U.1)))
    (U : X.affineOpens) (x : X) (hxU : x ∈ U.1) (hx : I ≤ (f.base x).asIdeal) :
    ∃ (r : Γ(X, U.1)) (g : G.obj U.1), x ∈ X.basicOpen r ∧
      Function.Bijective fun b : Γ(X, X.basicOpen r) => b • G.res (X.basicOpen_le r) g :=
  P2mLBLocal.main I f L hL G hGc hGq ψ hψs hψk U x hxU hx

end S_AlgebraicGeometry_OModulePresheaf_exists_basicOpen_bijective_smul_res_of_affHom_pushforward_adicThickening_of_le_asIdeal
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_basicOpen_bijective_smul_res_of_affHom_pushforward_adicThickening_of_le_asIdeal (solution)
