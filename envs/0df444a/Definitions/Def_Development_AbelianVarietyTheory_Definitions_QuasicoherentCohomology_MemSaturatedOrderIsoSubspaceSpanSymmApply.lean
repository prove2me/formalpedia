-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
-- name    : Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:25:32.423844+00:00
-- url     : https://prove2.me/theorems/7df2a5e8-8bff-4175-b8c4-06bdae7130ed
-- title:
--   Mem Saturated Order Iso Subspace Span Symm Apply
-- statement:
--   Definitions and structural lemmas for Mem Saturated Order Iso Subspace Span Symm Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/MemSaturatedOrderIsoSubspaceSpanSymmApply.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors Pointwise
namespace GlobalTheory
section Basic
variable {R : Type*} [CommRing R] {M M' : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M']
def saturation (N : Submodule R M) : Submodule R M :=
  (Submodule.torsion R (M ⧸ N)).comap N.mkQ
def IsSaturatedSubmodule (N : Submodule R M) : Prop :=
  saturation N = N
theorem mem_saturation_iff' {N : Submodule R M} {x : M} :
    x ∈ saturation N ↔ ∃ a ∈ R⁰, a • x ∈ N := by
  change N.mkQ x ∈ Submodule.torsion R (M ⧸ N) ↔ _
  rw [Submodule.mem_torsion_iff]
  constructor
  · rintro ⟨⟨a, ha⟩, h⟩
    refine ⟨a, ha, ?_⟩
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
    exact h
  · rintro ⟨a, ha, h⟩
    refine ⟨⟨a, ha⟩, ?_⟩
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul] at h
    exact h
theorem mem_saturation_iff [IsDomain R] {N : Submodule R M} {x : M} :
    x ∈ saturation N ↔ ∃ a : R, a ≠ 0 ∧ a • x ∈ N := by
  rw [mem_saturation_iff']
  simp only [mem_nonZeroDivisors_iff_ne_zero]
theorem mem_saturation_of_smul_mem [IsDomain R] {N : Submodule R M} {a : R} {x : M} (ha : a ≠ 0)
    (hx : a • x ∈ N) : x ∈ saturation N := mem_saturation_iff.2 ⟨a, ha, hx⟩
theorem le_saturation (N : Submodule R M) : N ≤ saturation N := fun x hx => mem_saturation_iff'.2 ⟨1, one_mem _, by rwa [one_smul]⟩
@[gcongr]
theorem saturation_mono {N N' : Submodule R M} (h : N ≤ N') : saturation N ≤ saturation N' := by
  intro x hx
  obtain ⟨a, ha, hax⟩ := mem_saturation_iff'.1 hx
  exact mem_saturation_iff'.2 ⟨a, ha, h hax⟩
@[simp]
theorem saturation_saturation (N : Submodule R M) : saturation (saturation N) = saturation N := by
  refine le_antisymm (fun x hx => ?_) (le_saturation _)
  obtain ⟨a, ha, hax⟩ := mem_saturation_iff'.1 hx
  obtain ⟨b, hb, hbx⟩ := mem_saturation_iff'.1 hax
  refine mem_saturation_iff'.2 ⟨b * a, mul_mem hb ha, ?_⟩
  rwa [mul_smul]
variable (R M) in

def saturationClosure : ClosureOperator (Submodule R M) where
  toFun := saturation
  monotone' _ _ := saturation_mono
  le_closure' := le_saturation
  idempotent' := saturation_saturation
  IsClosed := IsSaturatedSubmodule
  isClosed_iff := Iff.rfl
@[simp]
theorem saturationClosure_apply (N : Submodule R M) :
    saturationClosure R M N = saturation N := rfl
@[simp]
theorem saturationClosure_isClosed_iff (N : Submodule R M) :
    (saturationClosure R M).IsClosed N ↔ IsSaturatedSubmodule N := by rfl
theorem IsSaturatedSubmodule.saturation_eq {N : Submodule R M} (h : IsSaturatedSubmodule N) :
    saturation N = N := h
theorem isSaturatedSubmodule_iff_le {N : Submodule R M} :
    IsSaturatedSubmodule N ↔ saturation N ≤ N := ⟨fun h => h.saturation_eq.le, fun h => le_antisymm h (le_saturation N)⟩
theorem isSaturatedSubmodule_iff' {N : Submodule R M} :
    IsSaturatedSubmodule N ↔ ∀ a ∈ R⁰, ∀ x : M, a • x ∈ N → x ∈ N := by
  rw [isSaturatedSubmodule_iff_le]
  constructor
  · intro h a ha x hx
    exact h (mem_saturation_iff'.2 ⟨a, ha, hx⟩)
  · intro h x hx
    obtain ⟨a, ha, hax⟩ := mem_saturation_iff'.1 hx
    exact h a ha x hax
theorem isSaturatedSubmodule_iff [IsDomain R] {N : Submodule R M} :
    IsSaturatedSubmodule N ↔ ∀ a : R, a ≠ 0 → ∀ x : M, a • x ∈ N → x ∈ N := by
  rw [isSaturatedSubmodule_iff']
  simp only [mem_nonZeroDivisors_iff_ne_zero]
theorem IsSaturatedSubmodule.mem_of_smul_mem [IsDomain R] {N : Submodule R M}
    (h : IsSaturatedSubmodule N) {a : R} (ha : a ≠ 0) {x : M} (hx : a • x ∈ N) : x ∈ N := isSaturatedSubmodule_iff.1 h a ha x hx
theorem isSaturatedSubmodule_iff_torsion_eq_bot {N : Submodule R M} :
    IsSaturatedSubmodule N ↔ Submodule.torsion R (M ⧸ N) = ⊥ := by
  rw [isSaturatedSubmodule_iff_le, Submodule.eq_bot_iff]
  constructor
  · intro h y hy
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective N y
    exact (Submodule.Quotient.mk_eq_zero N).2 (h (show x ∈ saturation N from hy))
  · intro h x hx
    exact (Submodule.Quotient.mk_eq_zero N).1 (h (N.mkQ x) hx)
theorem isSaturatedSubmodule_iff_isTorsionFree [IsDomain R] {N : Submodule R M} :
    IsSaturatedSubmodule N ↔ Module.IsTorsionFree R (M ⧸ N) := by
  rw [isSaturatedSubmodule_iff_torsion_eq_bot, Submodule.isTorsionFree_iff_torsion_eq_bot]
theorem IsSaturatedSubmodule.isTorsionFree_quotient [IsDomain R] {N : Submodule R M}
    (h : IsSaturatedSubmodule N) : Module.IsTorsionFree R (M ⧸ N) := isSaturatedSubmodule_iff_isTorsionFree.1 h
theorem isSaturatedSubmodule_saturation (N : Submodule R M) :
    IsSaturatedSubmodule (saturation N) := by
  rw [isSaturatedSubmodule_iff_le, saturation_saturation]
instance isTorsionFree_quotient_saturation [IsDomain R] (N : Submodule R M) :
    Module.IsTorsionFree R (M ⧸ saturation N) :=
  (isSaturatedSubmodule_saturation N).isTorsionFree_quotient
theorem IsSaturatedSubmodule.saturation_le_iff {N P : Submodule R M}
    (h : IsSaturatedSubmodule P) : saturation N ≤ P ↔ N ≤ P := ⟨fun hN => (le_saturation N).trans hN, fun hN => (saturation_mono hN).trans h.saturation_eq.le⟩
theorem IsSaturatedSubmodule.eq_saturation {N P : Submodule R M}
    (h : IsSaturatedSubmodule P) (h₁ : N ≤ P) (h₂ : P ≤ saturation N) : P = saturation N := le_antisymm h₂ (h.saturation_le_iff.2 h₁)
@[simp]
theorem saturation_bot : saturation (⊥ : Submodule R M) = Submodule.torsion R M := by
  ext x
  rw [mem_saturation_iff', Submodule.mem_torsion_iff]
  simp only [Submodule.mem_bot]
  exact ⟨fun ⟨a, ha, h⟩ => ⟨⟨a, ha⟩, h⟩, fun ⟨a, h⟩ => ⟨a, a.2, h⟩⟩
@[simp]
theorem saturation_top : saturation (⊤ : Submodule R M) = ⊤ := top_unique (le_saturation _)
theorem saturation_inf (N P : Submodule R M) :
    saturation (N ⊓ P) = saturation N ⊓ saturation P := by
  refine le_antisymm (le_inf (saturation_mono inf_le_left) (saturation_mono inf_le_right)) ?_
  intro x hx
  obtain ⟨hN, hP⟩ := Submodule.mem_inf.1 hx
  obtain ⟨a, ha, hax⟩ := mem_saturation_iff'.1 hN
  obtain ⟨b, hb, hbx⟩ := mem_saturation_iff'.1 hP
  refine mem_saturation_iff'.2 ⟨a * b, mul_mem ha hb, Submodule.mem_inf.2 ⟨?_, ?_⟩⟩
  · rw [mul_comm, mul_smul]
    exact N.smul_mem b hax
  · rw [mul_smul]
    exact P.smul_mem a hbx
theorem saturation_comap (f : M →ₗ[R] M') (N : Submodule R M') :
    saturation (N.comap f) = (saturation N).comap f := by
  ext x
  simp only [Submodule.mem_comap, mem_saturation_iff', map_smul]
theorem IsSaturatedSubmodule.comap {N : Submodule R M'} (h : IsSaturatedSubmodule N)
    (f : M →ₗ[R] M') : IsSaturatedSubmodule (N.comap f) := by
  unfold IsSaturatedSubmodule
  rw [saturation_comap, h.saturation_eq]
end Basic
section Rank
variable {R : Type*} [CommRing R] [IsDomain R] {M : Type*} [AddCommGroup M] [Module R M]
end Rank
section Relative
variable {R : Type*} [CommRing R] {V V' : Type*} [AddCommGroup V] [Module R V]
  [AddCommGroup V'] [Module R V']
def saturationIn (M N : Submodule R V) : Submodule R V :=
  M ⊓ saturation N
def IsSaturatedIn (M N : Submodule R V) : Prop :=
  saturationIn M N = N
theorem saturationIn_def (M N : Submodule R V) : saturationIn M N = M ⊓ saturation N := rfl
theorem saturationIn_le (M N : Submodule R V) : saturationIn M N ≤ M := inf_le_left
theorem le_saturationIn {M N : Submodule R V} (h : N ≤ M) : N ≤ saturationIn M N := le_inf h (le_saturation N)
@[gcongr]
theorem saturationIn_mono {M M' N N' : Submodule R V} (hM : M ≤ M') (hN : N ≤ N') :
    saturationIn M N ≤ saturationIn M' N' := inf_le_inf hM (saturation_mono hN)
@[simp]
theorem saturationIn_top (N : Submodule R V) : saturationIn ⊤ N = saturation N := by
  rw [saturationIn_def, top_inf_eq]
@[simp]
theorem isSaturatedIn_top_iff {N : Submodule R V} :
    IsSaturatedIn ⊤ N ↔ IsSaturatedSubmodule N := by
  unfold IsSaturatedIn IsSaturatedSubmodule
  rw [saturationIn_top]
theorem saturationIn_inf (M N : Submodule R V) : saturationIn M (M ⊓ N) = saturationIn M N := by
  rw [saturationIn_def, saturationIn_def, saturation_inf, ← inf_assoc,
    inf_of_le_left (le_saturation M)]
@[simp]
theorem saturationIn_saturationIn (M N : Submodule R V) :
    saturationIn M (saturationIn M N) = saturationIn M N := by
  rw [saturationIn_def, saturationIn_def, saturation_inf, saturation_saturation, ← inf_assoc,
    inf_of_le_left (le_saturation M)]
theorem IsSaturatedIn.le {M N : Submodule R V} (h : IsSaturatedIn M N) : N ≤ M := by
  have h' : saturationIn M N = N := h
  rw [← h']
  exact saturationIn_le M N
theorem IsSaturatedIn.saturationIn_eq {M N : Submodule R V} (h : IsSaturatedIn M N) :
    saturationIn M N = N := h
theorem IsSaturatedSubmodule.isSaturatedIn_inf {W : Submodule R V} (h : IsSaturatedSubmodule W)
    (M : Submodule R V) : IsSaturatedIn M (M ⊓ W) := by
  unfold IsSaturatedIn
  rw [saturationIn_inf, saturationIn_def, h.saturation_eq]
theorem IsSaturatedIn.trans {M P N : Submodule R V} (hP : IsSaturatedIn M P)
    (hN : IsSaturatedIn P N) : IsSaturatedIn M N := by
  have hNP := hN.le
  have hPM := hP.le
  show saturationIn M N = N
  refine le_antisymm (fun x hx => ?_) (le_saturationIn (hNP.trans hPM))
  rw [saturationIn_def, Submodule.mem_inf] at hx
  have hxP : x ∈ P := by
    rw [← hP.saturationIn_eq, saturationIn_def]
    exact Submodule.mem_inf.2 ⟨hx.1, saturation_mono hNP hx.2⟩
  rw [← hN.saturationIn_eq, saturationIn_def]
  exact Submodule.mem_inf.2 ⟨hxP, hx.2⟩
end Relative
section Localisation
variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  (S : Type*) [CommRing S] [Algebra R S] (p : Submonoid R) [IsLocalization p S]
  {Mp : Type*} [AddCommGroup Mp] [Module R Mp] [Module S Mp] [IsScalarTower R S Mp]
  (f : M →ₗ[R] Mp) [IsLocalizedModule p f]
theorem mk'_mem_localized'_iff (N : Submodule R M) (x : M) (s : p) :
    IsLocalizedModule.mk' f x s ∈ N.localized' S p f ↔ ∃ a ∈ p, a • x ∈ N := by
  rw [Submodule.mem_localized']
  constructor
  · rintro ⟨m, hm, t, ht⟩
    obtain ⟨c, hc⟩ := (IsLocalizedModule.mk'_eq_mk'_iff f m x t s).1 ht
    refine ⟨((c * t : p) : R), (c * t).2, ?_⟩
    have e : ((c * t : p) : R) • x = ((c * s : p) : R) • m := by
      simp only [Submonoid.coe_mul, mul_smul]
      simpa only [Submonoid.smul_def] using hc
    rw [e]
    exact N.smul_mem _ hm
  · rintro ⟨a, ha, hax⟩
    exact ⟨a • x, hax, ⟨a, ha⟩ * s, IsLocalizedModule.mk'_cancel_left f x ⟨a, ha⟩ s⟩
theorem localized'_saturation (hp : p ≤ R⁰) (N : Submodule R M) :
    (saturation N).localized' S p f = saturation (N.localized' S p f) := by
  apply le_antisymm
  · refine ((Submodule.localized'gi S p f).gc _ _).2 fun m hm => ?_
    obtain ⟨a, ha, ham⟩ := mem_saturation_iff'.1 hm
    rw [Submodule.mem_comap, Submodule.restrictScalars_mem]
    refine mem_saturation_iff'.2
      ⟨algebraMap R S a, IsLocalization.nonZeroDivisors_le_comap (M := p) (S := S) ha, ?_⟩
    rw [algebraMap_smul, ← map_smul]
    exact (Submodule.mem_localized' S p f N _).2 ⟨a • m, ham, 1, IsLocalizedModule.mk'_one p f _⟩
  · intro y hy
    obtain ⟨b, hb, hby⟩ := mem_saturation_iff'.1 hy
    obtain ⟨⟨m, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective p f y
    obtain ⟨⟨r, t⟩, rfl⟩ := IsLocalization.mk'_surjective p b
    simp only [Function.uncurry_apply_pair] at hby ⊢
    rw [IsLocalizedModule.mk'_smul_mk', mk'_mem_localized'_iff] at hby
    obtain ⟨c, hc, hcr⟩ := hby
    have hr : r ∈ R⁰ := by
      have h1 : algebraMap R S r ∈ S⁰ := by
        rw [← IsLocalization.mk'_spec S r t]
        exact mul_mem hb (IsLocalization.map_units S t).mem_nonZeroDivisors
      exact mem_nonZeroDivisors_of_injective (IsLocalization.injective S hp) h1
    refine (Submodule.mem_localized' S p f _ _).2
      ⟨m, mem_saturation_iff'.2 ⟨c * r, mul_mem (hp hc) hr, ?_⟩, s, rfl⟩
    rwa [mul_smul]
theorem IsSaturatedSubmodule.localized' (hp : p ≤ R⁰) {N : Submodule R M}
    (h : IsSaturatedSubmodule N) : IsSaturatedSubmodule (N.localized' S p f) := by
  unfold IsSaturatedSubmodule
  rw [← localized'_saturation S p f hp, h.saturation_eq]
theorem IsSaturatedSubmodule.comap_localized' (hp : p ≤ R⁰) {N : Submodule R M}
    (h : IsSaturatedSubmodule N) : ((N.localized' S p f).restrictScalars R).comap f = N := by
  refine le_antisymm (fun m hm => ?_) (((Submodule.localized'gi S p f).gc _ _).1 le_rfl)
  rw [Submodule.mem_comap, Submodule.restrictScalars_mem, ← IsLocalizedModule.mk'_one p f m,
    mk'_mem_localized'_iff] at hm
  obtain ⟨a, ha, ham⟩ := hm
  exact h.saturation_eq.le (mem_saturation_iff'.2 ⟨a, hp ha, ham⟩)
end Localisation
section AmbientLocalisation
variable {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S] (p : Submonoid R)
  [IsLocalization p S] {V : Type*} [AddCommGroup V] [Module R V] [Module S V]
  [IsScalarTower R S V]
include p
theorem mem_span_localization_iff (N : Submodule R V) (x : V) :
    x ∈ Submodule.span S (N : Set V) ↔ ∃ a ∈ p, a • x ∈ N := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact ⟨1, one_mem _, by rwa [one_smul]⟩
    | zero => exact ⟨1, one_mem _, by rw [smul_zero]; exact N.zero_mem⟩
    | add y z _ _ hy hz =>
      obtain ⟨a, ha, hay⟩ := hy
      obtain ⟨b, hb, hbz⟩ := hz
      refine ⟨a * b, mul_mem ha hb, ?_⟩
      rw [smul_add]
      refine N.add_mem ?_ ?_
      · rw [mul_comm, mul_smul]
        exact N.smul_mem b hay
      · rw [mul_smul]
        exact N.smul_mem a hbz
    | smul s y _ hy =>
      obtain ⟨a, ha, hay⟩ := hy
      obtain ⟨⟨r, t⟩, rfl⟩ := IsLocalization.mk'_surjective p s
      refine ⟨(t : R) * a, mul_mem t.2 ha, ?_⟩
      have e : ((t : R) * a) • (IsLocalization.mk' S r t • y) = r • (a • y) := by
        rw [mul_smul, smul_comm a (IsLocalization.mk' S r t) y, ← algebraMap_smul S (t : R),
          smul_smul (algebraMap R S t), IsLocalization.mk'_spec', algebraMap_smul]
      rw [e]
      exact N.smul_mem r hay
  · rintro ⟨a, ha, hax⟩
    have hu : IsUnit (algebraMap R S a) := IsLocalization.map_units S (⟨a, ha⟩ : p)
    rw [← Submodule.smul_mem_iff_of_isUnit _ hu, algebraMap_smul]
    exact Submodule.subset_span hax
theorem isLocalizedModule_inclusionSpan (M : Submodule R V) :
    IsLocalizedModule p (M.inclusionSpan S) where
  map_units := by
    intro x
    rw [Module.End.isUnit_iff]
    have hu : IsUnit (algebraMap R S x) := IsLocalization.map_units S x
    constructor
    · intro y z hyz
      simp only [Module.algebraMap_end_apply] at hyz
      rw [← algebraMap_smul S (x : R) y, ← algebraMap_smul S (x : R) z] at hyz
      exact (hu.smul_left_cancel).1 hyz
    · intro y
      obtain ⟨u, hu'⟩ := hu
      refine ⟨(↑u⁻¹ : S) • y, ?_⟩
      simp only [Module.algebraMap_end_apply]
      rw [← algebraMap_smul S (x : R), smul_smul, ← hu', Units.mul_inv, one_smul]
  surj y := by
    obtain ⟨a, ha, hay⟩ := (mem_span_localization_iff S p M (y : V)).1 y.2
    exact ⟨(⟨a • (y : V), hay⟩, ⟨a, ha⟩), Subtype.ext rfl⟩
  exists_of_eq {x₁ x₂} h := ⟨1, by
    rw [one_smul, one_smul]
    exact Submodule.injective_inclusionSpan (p := M) (S := S) h⟩
theorem span_localization_inf (M N : Submodule R V) :
    Submodule.span S ((M ⊓ N : Submodule R V) : Set V) =
      Submodule.span S (M : Set V) ⊓ Submodule.span S (N : Set V) := by
  refine le_antisymm (le_inf (Submodule.span_mono fun _ hx => (Submodule.mem_inf.1 hx).1)
    (Submodule.span_mono fun _ hx => (Submodule.mem_inf.1 hx).2)) ?_
  intro x hx
  obtain ⟨hM, hN⟩ := Submodule.mem_inf.1 hx
  obtain ⟨a, ha, hax⟩ := (mem_span_localization_iff S p M x).1 hM
  obtain ⟨b, hb, hbx⟩ := (mem_span_localization_iff S p N x).1 hN
  refine (mem_span_localization_iff S p (M ⊓ N) x).2
    ⟨a * b, mul_mem ha hb, Submodule.mem_inf.2 ⟨?_, ?_⟩⟩
  · rw [mul_comm, mul_smul]
    exact M.smul_mem b hax
  · rw [mul_smul]
    exact N.smul_mem a hbx
theorem span_localization_inf_restrictScalars (M : Submodule R V) (W : Submodule S V) :
    Submodule.span S ((M ⊓ W.restrictScalars R : Submodule R V) : Set V) =
      Submodule.span S (M : Set V) ⊓ W := by
  rw [span_localization_inf S p, Submodule.coe_restrictScalars, Submodule.span_eq]
end AmbientLocalisation
section GenericFibre
variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
  {V : Type*} [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
  (f : M →ₗ[R] V) [IsLocalizedModule R⁰ f]
theorem saturation_eq_comap_localized' (N : Submodule R M) :
    saturation N = ((N.localized' K R⁰ f).restrictScalars R).comap f := by
  ext x
  rw [Submodule.mem_comap, Submodule.restrictScalars_mem, ← IsLocalizedModule.mk'_one R⁰ f x,
    mk'_mem_localized'_iff, mem_saturation_iff']
def saturatedOrderIsoSubspace :
    {N : Submodule R M // IsSaturatedSubmodule N} ≃o Submodule K V where
  toFun N := N.1.localized' K R⁰ f
  invFun W := ⟨(W.restrictScalars R).comap f, by
    rw [IsSaturatedSubmodule, saturation_eq_comap_localized' K f,
      (Submodule.localized'gi K R⁰ f).l_u_eq W]⟩
  left_inv N := Subtype.ext (N.2.comap_localized' K R⁰ f le_rfl)
  right_inv W := (Submodule.localized'gi K R⁰ f).l_u_eq W
  map_rel_iff' {N P} := by
    refine ((Submodule.localized'gi K R⁰ f).gc N.1 (P.1.localized' K R⁰ f)).trans ?_
    rw [P.2.comap_localized' K R⁰ f le_rfl]
    rfl
@[simp]
theorem saturatedOrderIsoSubspace_symm_apply (W : Submodule K V) :
    ((saturatedOrderIsoSubspace K f).symm W).1 = (W.restrictScalars R).comap f := rfl
end GenericFibre
section Lattice
variable {R : Type*} [CommRing R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
  {V : Type*} [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
theorem saturation_eq_span (N : Submodule R V) :
    saturation N = (Submodule.span K (N : Set V)).restrictScalars R := by
  ext x
  rw [Submodule.restrictScalars_mem, mem_span_localization_iff K R⁰ N x, mem_saturation_iff']
theorem saturationIn_eq_inf_span (M N : Submodule R V) :
    saturationIn M N = M ⊓ (Submodule.span K (N : Set V)).restrictScalars R := by
  rw [saturationIn_def, saturation_eq_span K]
variable {K} in

theorem isSaturatedSubmodule_restrictScalars (W : Submodule K V) :
    IsSaturatedSubmodule (W.restrictScalars R) := by
  unfold IsSaturatedSubmodule
  rw [saturation_eq_span K, Submodule.coe_restrictScalars, Submodule.span_eq]
variable {K} in

theorem isSaturatedIn_inf_restrictScalars (M : Submodule R V) (W : Submodule K V) :
    IsSaturatedIn M (M ⊓ W.restrictScalars R) := (isSaturatedSubmodule_restrictScalars W).isSaturatedIn_inf M
theorem isSaturatedIn_iff_inf_span_eq {M N : Submodule R V} :
    IsSaturatedIn M N ↔ M ⊓ (Submodule.span K (N : Set V)).restrictScalars R = N := by
  unfold IsSaturatedIn
  rw [saturationIn_eq_inf_span K]
variable {K} in

theorem span_inf_restrictScalars (M : Submodule R V) (W : Submodule K V) :
    Submodule.span K ((M ⊓ W.restrictScalars R : Submodule R V) : Set V) =
      Submodule.span K (M : Set V) ⊓ W := span_localization_inf_restrictScalars K R⁰ M W
variable {K} in

theorem span_inf_restrictScalars_of_le {M : Submodule R V} {W : Submodule K V}
    (h : W ≤ Submodule.span K (M : Set V)) :
    Submodule.span K ((M ⊓ W.restrictScalars R : Submodule R V) : Set V) = W := by
  rw [span_inf_restrictScalars, inf_of_le_right h]
def saturatedOrderIsoSubspaceSpan (M : Submodule R V) :
    {N : Submodule R M // IsSaturatedSubmodule N} ≃o
      Submodule K (Submodule.span K (M : Set V)) :=
  haveI := isLocalizedModule_inclusionSpan K R⁰ M
  saturatedOrderIsoSubspace K (M.inclusionSpan K)
def saturatedInOrderIso (M : Submodule R V) :
    {N : Submodule R V // IsSaturatedIn M N} ≃o Set.Iic (Submodule.span K (M : Set V)) where
  toFun N := ⟨Submodule.span K (N.1 : Set V), Submodule.span_mono N.2.le⟩
  invFun W := ⟨M ⊓ W.1.restrictScalars R, isSaturatedIn_inf_restrictScalars M W.1⟩
  left_inv N := Subtype.ext ((isSaturatedIn_iff_inf_span_eq K).1 N.2)
  right_inv W := Subtype.ext (span_inf_restrictScalars_of_le W.2)
  map_rel_iff' {N P} := by
    refine ⟨fun h => ?_, fun h => Submodule.span_mono h⟩
    change N.1 ≤ P.1
    rw [← (isSaturatedIn_iff_inf_span_eq K).1 P.2]
    exact le_inf N.2.le fun x hx => h (Submodule.subset_span hx)
@[simp]
theorem saturatedInOrderIso_apply (M : Submodule R V)
    (N : {N : Submodule R V // IsSaturatedIn M N}) :
    (saturatedInOrderIso K M N).1 = Submodule.span K (N.1 : Set V) := rfl
@[simp]
theorem saturatedInOrderIso_symm_apply (M : Submodule R V)
    (W : Set.Iic (Submodule.span K (M : Set V))) :
    ((saturatedInOrderIso K M).symm W).1 = M ⊓ W.1.restrictScalars R := rfl
end Lattice
section Examples
theorem isSaturatedSubmodule_span_one_two :
    IsSaturatedSubmodule (Submodule.span ℤ {((1, 2) : ℤ × ℤ)}) := by
  rw [isSaturatedSubmodule_iff]
  intro a ha x hx
  rw [Submodule.mem_span_singleton] at hx ⊢
  obtain ⟨k, hk⟩ := hx
  have h1 : k = a * x.1 := by simpa using congrArg Prod.fst hk
  have h2 : k * 2 = a * x.2 := by simpa using congrArg Prod.snd hk
  refine ⟨x.1, Prod.ext ?_ ?_⟩
  · simp
  · have h3 : a * (x.1 * 2) = a * x.2 := by linear_combination (-2 : ℤ) * h1 + h2
    simpa using mul_left_cancel₀ ha h3
example : saturation (Submodule.span ℤ {((3, 6) : ℤ × ℤ)}) =
    Submodule.span ℤ {((1, 2) : ℤ × ℤ)} := by
  refine (isSaturatedSubmodule_span_one_two.eq_saturation ?_ ?_).symm
  · rw [Submodule.span_singleton_le_iff_mem]
    exact Submodule.mem_span_singleton.2 ⟨3, rfl⟩
  · rw [Submodule.span_singleton_le_iff_mem]
    exact mem_saturation_of_smul_mem (a := 3) (by norm_num) (Submodule.mem_span_singleton_self _)
example : ¬ IsSaturatedSubmodule (Submodule.span ℤ {(2 : ℤ)}) := by
  intro h
  have h₁ : (1 : ℤ) ∈ Submodule.span ℤ {(2 : ℤ)} :=
    h.mem_of_smul_mem (a := 2) (by norm_num) (Submodule.mem_span_singleton_self _)
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.1 h₁
  simp only [smul_eq_mul] at hb
  omega
example : saturation (⊥ : Submodule ℤ (ZMod 2)) = ⊤ :=
  top_le_iff.1 fun x _ => mem_saturation_of_smul_mem (a := 2) (by norm_num) (by
    rw [Submodule.mem_bot]; exact (by decide : ∀ y : ZMod 2, (2 : ℤ) • y = 0) x)
example : saturationIn (Submodule.span ℤ {(2 : ℚ)}) (Submodule.span ℤ {(6 : ℚ)}) =
      Submodule.span ℤ {(2 : ℚ)} ∧ saturation (Submodule.span ℤ {(6 : ℚ)}) = ⊤ := by
  have h : saturation (Submodule.span ℤ {(6 : ℚ)}) = ⊤ := by
    rw [saturation_eq_span ℚ, Submodule.span_span_of_tower, Submodule.restrictScalars_eq_top_iff,
      Submodule.span_singleton_eq_top_iff]
    intro v
    exact ⟨v / 6, by simp⟩
  exact ⟨by rw [saturationIn, h, inf_top_eq], h⟩
end Examples
end GlobalTheory


