-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:30:47.257464+00:00
-- url     : https://prove2.me/theorems/db9adc07-692b-4be8-9e01-ae5c8fdeef00
-- title:
--   Exists Finite Projective Complex Quasi Iso
-- statement:
--   Definitions and structural lemmas for Exists Finite Projective Complex Quasi Iso, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsFiniteProjectiveComplexQuasiIso.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory TensorProduct
universe u v w
namespace GlobalTheory
section Flat
variable {R : Type u} [CommRing R] {A B C D : Type*} [AddCommGroup A] [AddCommGroup B]
  [AddCommGroup C] [AddCommGroup D] [Module R A] [Module R B] [Module R C] [Module R D]
theorem flat_of_shortExact_of_flat_of_flat (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hf : Function.Injective f) (hg : Function.Surjective g) (h : Function.Exact f g)
    [Module.Flat R B] [Module.Flat R C] : Module.Flat R A := by
  rw [Module.Flat.iff_rTensor_injective']
  intro I
  have h1 := LinearMap.lTensor_injective_of_exact_of_flat g hg f hf h I
  have h2 := Module.Flat.rTensor_preserves_injective_linearMap (M := B) I.subtype
    I.subtype_injective
  have h3 : (f.lTensor R) ∘ₗ (I.subtype.rTensor A) = (I.subtype.rTensor B) ∘ₗ (f.lTensor I) := by
    simp
  have h4 : Function.Injective ((f.lTensor R) ∘ₗ (I.subtype.rTensor A)) := by
    rw [h3]; exact h2.comp h1
  exact Function.Injective.of_comp (f := f.lTensor R) h4
theorem flat_prod [Module.Flat R A] [Module.Flat R B] : Module.Flat R (A × B) := by
  rw [Module.Flat.iff_rTensor_injective']
  intro I
  have h1 := Module.Flat.rTensor_preserves_injective_linearMap (M := A) I.subtype
    I.subtype_injective
  have h2 := Module.Flat.rTensor_preserves_injective_linearMap (M := B) I.subtype
    I.subtype_injective
  have e : ∀ x, TensorProduct.prodRight R R R A B (I.subtype.rTensor (A × B) x) =
      Prod.map (I.subtype.rTensor A) (I.subtype.rTensor B)
        (TensorProduct.prodRight R R I A B x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]; ext <;> simp
    | tmul m y => simp
    | add x y hx hy => simp only [map_add, hx, hy]; ext <;> simp
  intro x y hxy
  apply (TensorProduct.prodRight R R I A B).injective
  apply h1.prodMap h2
  rw [← e, ← e, hxy]
theorem exact_range_subtype_rangeRestrict {f : A →ₗ[R] B} {g : B →ₗ[R] C}
    (h : Function.Exact f g) : Function.Exact (LinearMap.range f).subtype g.rangeRestrict := by
  rw [LinearMap.exact_iff] at h ⊢
  rw [LinearMap.ker_rangeRestrict, h, Submodule.range_subtype]
theorem flat_range_of_exact {f : A →ₗ[R] B} {g : B →ₗ[R] C} (h : Function.Exact f g)
    [Module.Flat R B] [Module.Flat R (LinearMap.range g)] : Module.Flat R (LinearMap.range f) :=
  flat_of_shortExact_of_flat_of_flat _ _ (LinearMap.range f).subtype_injective
    g.surjective_rangeRestrict (exact_range_subtype_rangeRestrict h)
theorem lTensor_exact_of_flat_range {f : A →ₗ[R] B} {g : B →ₗ[R] C} {k : C →ₗ[R] D}
    (h : Function.Exact f g) (h' : Function.Exact g k) [Module.Flat R (LinearMap.range k)]
    (M : Type*) [AddCommGroup M] [Module R M] :
    Function.Exact (f.lTensor M) (g.lTensor M) := by
  have h1 := LinearMap.lTensor_injective_of_exact_of_flat k.rangeRestrict
    k.surjective_rangeRestrict _ (LinearMap.range g).subtype_injective
    (exact_range_subtype_rangeRestrict h') M
  have h2 : Function.Exact f g.rangeRestrict := by
    rw [LinearMap.exact_iff] at h ⊢
    rw [LinearMap.ker_rangeRestrict, h]
  have h3 := lTensor_exact M h2 g.surjective_rangeRestrict
  have h4 : g.lTensor M = ((LinearMap.range g).subtype.lTensor M) ∘ₗ (g.rangeRestrict.lTensor M) := by
    rw [← LinearMap.lTensor_comp]; rfl
  rw [LinearMap.exact_iff] at h3 ⊢
  rw [h4, LinearMap.ker_comp_of_ker_eq_bot _ (LinearMap.ker_eq_bot.2 h1), h3]
theorem flat_range_of_exact_of_bounded {E : ℕ → Type*} [∀ p, AddCommGroup (E p)]
    [∀ p, Module R (E p)] [∀ p, Module.Flat R (E p)] (D : ∀ p, E p →ₗ[R] E (p + 1))
    (hD : ∀ p, Function.Exact (D p) (D (p + 1))) (n : ℕ) (hn : ∀ p, n < p → Subsingleton (E p))
    (p : ℕ) : Module.Flat R (LinearMap.range (D p)) := by
  have key : ∀ m p, n < p + 1 + m → Module.Flat R (LinearMap.range (D p)) := by
    intro m
    induction m with
    | zero =>
      intro p hp
      have := hn (p + 1) hp
      infer_instance
    | succ m ih =>
      intro p hp
      have := ih (p + 1) (by omega)
      exact flat_range_of_exact (hD p)
  exact key n p (by omega)
end Flat
structure ConeExact {K : ℕ → Type v} {C : ℕ → Type w} [∀ p, AddCommGroup (K p)]
    [∀ p, AddCommGroup (C p)] (dK : ∀ p, K p → K (p + 1)) (dC : ∀ p, C p → C (p + 1))
    (φ : ∀ p, K p → C p) : Prop where
  inj : ∀ x : K 0, φ 0 x = 0 → dK 0 x = 0 → x = 0
  zero : ∀ (c : C 0) (k : K 1), dC 0 c = φ 1 k → dK 1 k = 0 → ∃ x : K 0, φ 0 x = c ∧ dK 0 x = k
  succ : ∀ (p : ℕ) (c : C (p + 1)) (k : K (p + 2)), dC (p + 1) c = φ (p + 2) k →
    dK (p + 2) k = 0 → ∃ (c' : C p) (k' : K (p + 1)),
      dC p c' + φ (p + 1) k' = c ∧ dK (p + 1) k' = k
section Cone
variable {R : Type u} [CommRing R] {K : ℕ → Type v} {C : ℕ → Type w} [∀ p, AddCommGroup (K p)]
  [∀ p, AddCommGroup (C p)] [∀ p, Module R (K p)] [∀ p, Module R (C p)]
def coneD (dK : ∀ p, K p →ₗ[R] K (p + 1)) (dC : ∀ p, C p →ₗ[R] C (p + 1))
    (φ : ∀ p, K p →ₗ[R] C p) (p : ℕ) : C p × K (p + 1) →ₗ[R] C (p + 1) × K (p + 2) :=
  ((dC p).coprod (-φ (p + 1))).prod (-(dK (p + 1)) ∘ₗ LinearMap.snd R _ _)
@[simp]
theorem coneD_apply (dK : ∀ p, K p →ₗ[R] K (p + 1)) (dC : ∀ p, C p →ₗ[R] C (p + 1))
    (φ : ∀ p, K p →ₗ[R] C p) (p : ℕ) (x : C p × K (p + 1)) :
    coneD dK dC φ p x = (dC p x.1 - φ (p + 1) x.2, - dK (p + 1) x.2) := by
  simp [coneD, sub_eq_add_neg]
variable {dK : ∀ p, K p →ₗ[R] K (p + 1)} {dC : ∀ p, C p →ₗ[R] C (p + 1)}
    {φ : ∀ p, K p →ₗ[R] C p}
theorem coneExact_iff (hK : ∀ p x, dK (p + 1) (dK p x) = 0) (hC : ∀ p x, dC (p + 1) (dC p x) = 0)
    (hφ : ∀ p x, dC p (φ p x) = φ (p + 1) (dK p x)) :
    ConeExact (fun p => dK p) (fun p => dC p) (fun p => φ p) ↔
      Function.Injective ((φ 0).prod (dK 0)) ∧
      Function.Exact ((φ 0).prod (dK 0)) (coneD dK dC φ 0) ∧
      ∀ p, Function.Exact (coneD dK dC φ p) (coneD dK dC φ (p + 1)) := by
  constructor
  · rintro ⟨h0, h1, h2⟩
    refine ⟨?_, ?_, fun p => ?_⟩
    · rw [injective_iff_map_eq_zero]
      intro x hx
      exact h0 x (congrArg Prod.fst hx) (congrArg Prod.snd hx)
    · rintro ⟨c, k⟩
      constructor
      · intro h
        simp only [coneD_apply, Prod.mk_eq_zero, sub_eq_zero, neg_eq_zero] at h
        obtain ⟨x, hx1, hx2⟩ := h1 c k h.1 h.2
        exact ⟨x, Prod.ext hx1 hx2⟩
      · rintro ⟨x, hx⟩
        rw [← hx]
        simp [hφ, hK]
    · rintro ⟨c, k⟩
      constructor
      · intro h
        simp only [coneD_apply, Prod.mk_eq_zero, sub_eq_zero, neg_eq_zero] at h
        obtain ⟨c', k', hx1, hx2⟩ := h2 p c k h.1 h.2
        refine ⟨(c', -k'), ?_⟩
        simp [hx1, hx2]
      · rintro ⟨x, hx⟩
        rw [← hx]
        simp [hφ, hK, hC]
  · rintro ⟨h0, h1, h2⟩
    refine ⟨fun x hx hx' => ?_, fun c k h h' => ?_, fun p c k h h' => ?_⟩
    · exact (injective_iff_map_eq_zero _).1 h0 x (Prod.ext hx hx')
    · obtain ⟨x, hx⟩ := (h1 (c, k)).1 (by simp [h, h'])
      exact ⟨x, congrArg Prod.fst hx, congrArg Prod.snd hx⟩
    · obtain ⟨⟨c', k'⟩, hx⟩ := (h2 p (c, k)).1 (by simp [h, h'])
      simp only [coneD_apply, Prod.mk.injEq] at hx
      exact ⟨c', -k', by simp [← hx.1, sub_eq_add_neg], by simp [← hx.2]⟩
theorem flat_range_coneD [∀ p, Module.Flat R (K (p + 1))] [∀ p, Module.Flat R (C p)]
    (h : ∀ p, Function.Exact (coneD dK dC φ p) (coneD dK dC φ (p + 1))) (n : ℕ)
    (hnK : ∀ p, n < p → Subsingleton (K p)) (hnC : ∀ p, n < p → Subsingleton (C p)) (p : ℕ) :
    Module.Flat R (LinearMap.range (coneD dK dC φ p)) := by
  have : ∀ p, Module.Flat R (C p × K (p + 1)) := fun p => flat_prod
  refine flat_range_of_exact_of_bounded (E := fun p => C p × K (p + 1)) _ h n (fun p hp => ?_) p
  have := hnK (p + 1) (by omega)
  have := hnC p hp
  infer_instance
theorem ConeExact.lTensor [∀ p, Module.Flat R (K (p + 1))] [∀ p, Module.Flat R (C p)]
    (h : ConeExact (fun p => dK p) (fun p => dC p) (fun p => φ p))
    (hK : ∀ p x, dK (p + 1) (dK p x) = 0) (hC : ∀ p x, dC (p + 1) (dC p x) = 0)
    (hφ : ∀ p x, dC p (φ p x) = φ (p + 1) (dK p x)) (n : ℕ)
    (hnK : ∀ p, n < p → Subsingleton (K p)) (hnC : ∀ p, n < p → Subsingleton (C p))
    (M : Type*) [AddCommGroup M] [Module R M] :
    ConeExact (fun p => (dK p).lTensor M) (fun p => (dC p).lTensor M)
      (fun p => (φ p).lTensor M) := by
  obtain ⟨h0, h1, h2⟩ := (coneExact_iff hK hC hφ).1 h
  have hfl := flat_range_coneD h2 n hnK hnC
  have e0 : ∀ x, ((φ 0).lTensor M).prod ((dK 0).lTensor M) x =
      TensorProduct.prodRight R R M _ _ (((φ 0).prod (dK 0)).lTensor M x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul m y => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  have e1 : ∀ p x, coneD (fun p => (dK p).lTensor M) (fun p => (dC p).lTensor M)
      (fun p => (φ p).lTensor M) p (TensorProduct.prodRight R R M _ _ x) =
      TensorProduct.prodRight R R M _ _ ((coneD dK dC φ p).lTensor M x) := by
    intro p x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul m y => simp [tmul_sub, tmul_neg]
    | add x y hx hy => simp only [map_add, hx, hy]
  refine (coneExact_iff (fun p x => ?_) (fun p x => ?_) (fun p x => ?_)).2 ⟨?_, ?_, fun p => ?_⟩
  · rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
      show dK (p + 1) ∘ₗ dK p = 0 from LinearMap.ext (hK p)]
    simp
  · rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
      show dC (p + 1) ∘ₗ dC p = 0 from LinearMap.ext (hC p)]
    simp
  · rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
      show dC p ∘ₗ φ p = φ (p + 1) ∘ₗ dK p from LinearMap.ext (hφ p), LinearMap.lTensor_comp,
      LinearMap.comp_apply]
  · have := hfl 0
    have h3 : Function.Exact ((φ 0).prod (dK 0)) (coneD dK dC φ 0).rangeRestrict := by
      rw [LinearMap.exact_iff] at h1 ⊢
      rw [LinearMap.ker_rangeRestrict, h1]
    have h4 := LinearMap.lTensor_injective_of_exact_of_flat _
      (coneD dK dC φ 0).surjective_rangeRestrict _ h0 h3 M
    intro x y hxy
    rw [e0, e0] at hxy
    exact h4 ((TensorProduct.prodRight R R M _ _).injective hxy)
  · have := hfl 1
    have h3 := lTensor_exact_of_flat_range h1 (h2 0) M
    intro y
    obtain ⟨y, rfl⟩ := (TensorProduct.prodRight R R M _ _).surjective y
    rw [e1, LinearEquiv.map_eq_zero_iff, h3 y]
    simp only [Set.mem_range, e0, EmbeddingLike.apply_eq_iff_eq]
  · have := hfl (p + 2)
    have h3 := lTensor_exact_of_flat_range (h2 p) (h2 (p + 1)) M
    intro y
    obtain ⟨y, rfl⟩ := (TensorProduct.prodRight R R M _ _).surjective y
    rw [e1, LinearEquiv.map_eq_zero_iff, h3 y]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨_, e1 p x⟩
    · rintro ⟨x, hx⟩
      obtain ⟨x, rfl⟩ := (TensorProduct.prodRight R R M _ _).surjective x
      rw [e1] at hx
      exact ⟨x, (TensorProduct.prodRight R R M _ _).injective hx⟩
end Cone
section Construction
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
end Construction
section QuasiIso
variable {R : Type u} [Ring R]
end QuasiIso
section Main
open Limits
variable {R : Type u} [CommRing R]
instance extendScalars_additive {S : Type w} [CommRing S] (f : R →+* S) :
    (ModuleCat.extendScalars.{u, w, v} f).Additive where
  map_add {M N} g h := by
    letI := f.toAlgebra
    ext m
    exact tmul_add (R := R) (1 : S) (g.hom m) (h.hom m)
end Main
end GlobalTheory


