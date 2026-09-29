-- Prove2me | solution 1 for AlgebraicGeometry.isPushout_specMap_of_isPullback_of_surjective_of_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/3020e733-f564-5001-9de8-b2b666aa3349

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isPushout_specMap_of_isPullback_of_surjective_of_isNilpotent

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace P2mThickeningPushout

variable {R C C' C₀ : Type u} [CommRing R] [CommRing C] [CommRing C'] [CommRing C₀]
  {π₁ : R →+* C} {π₂ : R →+* C'} {q : C →+* C₀} {q' : C' →+* C₀}

structure Setup (π₁ : R →+* C) (π₂ : R →+* C') (q : C →+* C₀) (q' : C' →+* C₀) : Prop where
  w : ∀ r : R, q (π₁ r) = q' (π₂ r)
  inj : ∀ x y : R, π₁ x = π₁ y → π₂ x = π₂ y → x = y
  lift : ∀ (c : C) (c' : C'), q c = q' c' → ∃ r : R, π₁ r = c ∧ π₂ r = c'
  surj : Function.Surjective q'
  nil : ∀ x : C', q' x = 0 → IsNilpotent x

namespace Setup

variable (S : Setup π₁ π₂ q q')
include S

lemma surj₁ : Function.Surjective π₁ := by
  intro c
  obtain ⟨c', hc'⟩ := S.surj (q c)
  obtain ⟨r, hr, -⟩ := S.lift c c' hc'.symm
  exact ⟨r, hr⟩

lemma nil₁ (x : R) (hx : π₁ x = 0) : IsNilpotent x := by
  have h2 : q' (π₂ x) = 0 := by rw [← S.w, hx, map_zero]
  obtain ⟨n, hn⟩ := S.nil _ h2
  refine ⟨n + 1, S.inj _ _ ?_ ?_⟩
  · rw [map_pow, hx, map_zero, zero_pow (Nat.succ_ne_zero n)]
  · rw [map_pow, pow_succ, hn, map_zero, zero_mul]

omit [CommRing R] [CommRing C] [CommRing C'] [CommRing C₀] S in

lemma comap_bijective_of_surjective_of_nil {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Surjective f) (hnil : ∀ x, f x = 0 → IsNilpotent x) :
    Function.Bijective (PrimeSpectrum.comap f) := by
  refine ⟨PrimeSpectrum.comap_injective_of_surjective f hf, ?_⟩
  rw [← Set.range_eq_univ, range_comap_of_surjective _ f hf,
    PrimeSpectrum.zeroLocus_eq_univ_iff]
  intro x hx
  exact hnil x hx

lemma bijective₁ : Function.Bijective (PrimeSpectrum.comap π₁) :=
  comap_bijective_of_surjective_of_nil π₁ S.surj₁ S.nil₁

lemma bijective' : Function.Bijective (PrimeSpectrum.comap q') :=
  comap_bijective_of_surjective_of_nil q' S.surj S.nil

section Loc

variable (s : R)

noncomputable abbrev ρ₁ (π₁ : R →+* C) (s : R) :
    Localization.Away s →+* Localization.Away (π₁ s) :=
  IsLocalization.Away.map _ _ π₁ s

noncomputable abbrev ρ₂ (π₂ : R →+* C') (s : R) :
    Localization.Away s →+* Localization.Away (π₂ s) :=
  IsLocalization.Away.map _ _ π₂ s

noncomputable abbrev κ₁ (π₁ : R →+* C) (q : C →+* C₀) (s : R) :
    Localization.Away (π₁ s) →+* Localization.Away (q (π₁ s)) :=
  IsLocalization.Away.map _ _ q (π₁ s)

omit S in
lemma powers_le_comap (s : R) (hw : ∀ r : R, q (π₁ r) = q' (π₂ r)) :
    Submonoid.powers (π₂ s) ≤ (Submonoid.powers (q (π₁ s))).comap q' := by
  rintro _ ⟨n, rfl⟩
  refine ⟨n, ?_⟩
  simp [map_pow, hw]

noncomputable def κ₂ : Localization.Away (π₂ s) →+* Localization.Away (q (π₁ s)) :=
  IsLocalization.map (M := Submonoid.powers (π₂ s)) (T := Submonoid.powers (q (π₁ s)))
    (Localization.Away (q (π₁ s))) q' (powers_le_comap s S.w)

lemma κ₂_algebraMap (x : C') :
    S.κ₂ s (algebraMap C' _ x) = algebraMap C₀ _ (q' x) := by
  simp [κ₂, IsLocalization.map_eq]

omit S in
lemma ρ₁_algebraMap (x : R) : ρ₁ π₁ s (algebraMap R _ x) = algebraMap C _ (π₁ x) := by
  simp [ρ₁, IsLocalization.Away.map, IsLocalization.map_eq]

omit S in
lemma ρ₂_algebraMap (x : R) : ρ₂ π₂ s (algebraMap R _ x) = algebraMap C' _ (π₂ x) := by
  simp [ρ₂, IsLocalization.Away.map, IsLocalization.map_eq]

omit S in
lemma κ₁_algebraMap (x : C) : κ₁ π₁ q s (algebraMap C _ x) = algebraMap C₀ _ (q x) := by
  simp [κ₁, IsLocalization.Away.map, IsLocalization.map_eq]

omit S in
lemma ρ₁_mk' (a : R) (n : ℕ) :
    ρ₁ π₁ s (IsLocalization.mk' (M := Submonoid.powers s) _ a ⟨s ^ n, n, rfl⟩) =
      IsLocalization.mk' (M := Submonoid.powers (π₁ s)) _ (π₁ a) ⟨π₁ s ^ n, n, rfl⟩ := by
  simp only [ρ₁, IsLocalization.Away.map, IsLocalization.map_mk']
  congr 1
  ext
  simp

omit S in
lemma ρ₂_mk' (a : R) (n : ℕ) :
    ρ₂ π₂ s (IsLocalization.mk' (M := Submonoid.powers s) _ a ⟨s ^ n, n, rfl⟩) =
      IsLocalization.mk' (M := Submonoid.powers (π₂ s)) _ (π₂ a) ⟨π₂ s ^ n, n, rfl⟩ := by
  simp only [ρ₂, IsLocalization.Away.map, IsLocalization.map_mk']
  congr 1
  ext
  simp

lemma inj_loc (x : Localization.Away s) (h₁ : ρ₁ π₁ s x = 0) (h₂ : ρ₂ π₂ s x = 0) : x = 0 := by
  obtain ⟨⟨a, _, n, rfl⟩, ha⟩ := IsLocalization.surj (Submonoid.powers s) x
  dsimp only at ha

  have ha₁ : algebraMap C _ (π₁ a) = (0 : Localization.Away (π₁ s)) := by
    have := congrArg (ρ₁ π₁ s) ha
    rw [map_mul, h₁, zero_mul, ρ₁_algebraMap] at this
    exact this.symm
  have ha₂ : algebraMap C' _ (π₂ a) = (0 : Localization.Away (π₂ s)) := by
    have := congrArg (ρ₂ π₂ s) ha
    rw [map_mul, h₂, zero_mul, ρ₂_algebraMap] at this
    exact this.symm
  rw [IsLocalization.map_eq_zero_iff (Submonoid.powers (π₁ s))] at ha₁
  rw [IsLocalization.map_eq_zero_iff (Submonoid.powers (π₂ s))] at ha₂
  obtain ⟨⟨_, m₁, rfl⟩, hm₁⟩ := ha₁
  obtain ⟨⟨_, m₂, rfl⟩, hm₂⟩ := ha₂
  dsimp only at hm₁ hm₂
  have hsa : s ^ (m₁ + m₂) * a = 0 := by
    refine S.inj _ _ ?_ ?_
    · rw [map_mul, map_pow, map_zero, pow_add, mul_comm (π₁ s ^ m₁), mul_assoc, hm₁, mul_zero]
    · rw [map_mul, map_pow, map_zero, pow_add, mul_assoc, hm₂, mul_zero]
  have hu : IsUnit (algebraMap R (Localization.Away s) (s ^ (m₁ + m₂ + n))) :=
    IsLocalization.map_units (M := Submonoid.powers s) _ ⟨s ^ (m₁ + m₂ + n), _, rfl⟩
  rw [← hu.mul_left_eq_zero]
  calc x * algebraMap R _ (s ^ (m₁ + m₂ + n))
      = algebraMap R _ (s ^ (m₁ + m₂)) * (x * algebraMap R _ (s ^ n)) := by
        rw [pow_add, map_mul]; ring
    _ = 0 := by rw [ha, ← map_mul, hsa, map_zero]

lemma lift_loc (y₁ : Localization.Away (π₁ s)) (y₂ : Localization.Away (π₂ s))
    (h : κ₁ π₁ q s y₁ = S.κ₂ s y₂) :
    ∃ x : Localization.Away s, ρ₁ π₁ s x = y₁ ∧ ρ₂ π₂ s x = y₂ := by
  obtain ⟨⟨a₁, _, n₁, rfl⟩, ha₁⟩ := IsLocalization.surj (Submonoid.powers (π₁ s)) y₁
  obtain ⟨⟨a₂, _, n₂, rfl⟩, ha₂⟩ := IsLocalization.surj (Submonoid.powers (π₂ s)) y₂
  dsimp only at ha₁ ha₂

  set N := n₁ + n₂ with hN
  have hb₁ : y₁ * algebraMap C _ (π₁ s ^ N) = algebraMap C _ (π₁ s ^ n₂ * a₁) := by
    rw [hN, pow_add, map_mul, map_mul, ← ha₁]; ring
  have hb₂ : y₂ * algebraMap C' _ (π₂ s ^ N) = algebraMap C' _ (π₂ s ^ n₁ * a₂) := by
    rw [hN, pow_add, map_mul, map_mul, ← ha₂]; ring
  set b₁ := π₁ s ^ n₂ * a₁
  set b₂ := π₂ s ^ n₁ * a₂
  clear_value b₁ b₂

  have hc₁ : κ₁ π₁ q s y₁ * algebraMap C₀ _ (q (π₁ s) ^ N) = algebraMap C₀ _ (q b₁) := by
    have := congrArg (κ₁ π₁ q s) hb₁
    rwa [map_mul, κ₁_algebraMap, κ₁_algebraMap, map_pow] at this
  have hc₂ : S.κ₂ s y₂ * algebraMap C₀ _ (q (π₁ s) ^ N) = algebraMap C₀ _ (q' b₂) := by
    have := congrArg (S.κ₂ s) hb₂
    rwa [map_mul, κ₂_algebraMap, κ₂_algebraMap, map_pow, ← S.w] at this
  have hq : algebraMap C₀ (Localization.Away (q (π₁ s))) (q b₁) = algebraMap C₀ _ (q' b₂) := by
    rw [← hc₁, ← hc₂, h]
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers (q (π₁ s))) _).mp hq
  dsimp only at hk

  have hpair : q (π₁ s ^ k * b₁) = q' (π₂ s ^ k * b₂) := by
    rw [map_mul, map_mul, map_pow, map_pow, ← S.w s, hk]
  obtain ⟨r, hr₁, hr₂⟩ := S.lift _ _ hpair
  refine ⟨IsLocalization.mk' (M := Submonoid.powers s) _ r ⟨s ^ (k + N), _, rfl⟩, ?_, ?_⟩
  · rw [ρ₁_mk', IsLocalization.mk'_eq_iff_eq_mul, hr₁]
    simp only [map_pow, pow_add, map_mul]
    rw [mul_comm _ (algebraMap C _ (π₁ s) ^ N), ← mul_assoc, ← map_pow _ _ N, hb₁, mul_comm]
  · rw [ρ₂_mk', IsLocalization.mk'_eq_iff_eq_mul, hr₂]
    simp only [map_pow, pow_add, map_mul]
    rw [mul_comm _ (algebraMap C' _ (π₂ s) ^ N), ← mul_assoc, ← map_pow _ _ N, hb₂, mul_comm]

lemma exists_comp_eq_loc {A : Type u} [CommRing A] (a₁ : A →+* Localization.Away (π₁ s))
    (a₂ : A →+* Localization.Away (π₂ s)) (h : (κ₁ π₁ q s).comp a₁ = (S.κ₂ s).comp a₂) :
    ∃ b : A →+* Localization.Away s, (ρ₁ π₁ s).comp b = a₁ ∧ (ρ₂ π₂ s).comp b = a₂ := by
  let θ : Localization.Away s →+* Localization.Away (π₁ s) × Localization.Away (π₂ s) :=
    (ρ₁ π₁ s).prod (ρ₂ π₂ s)
  have hθ : Function.Injective θ := by
    intro x y hxy
    rw [← sub_eq_zero]
    refine S.inj_loc s _ ?_ ?_
    · have := congrArg Prod.fst hxy
      simpa [θ, sub_eq_zero] using this
    · have := congrArg Prod.snd hxy
      simpa [θ, sub_eq_zero] using this
  let e : Localization.Away s ≃+* θ.range :=
    RingEquiv.ofBijective θ.rangeRestrict ⟨fun x y hxy => hθ (congrArg Subtype.val hxy),
      RingHom.rangeRestrict_surjective θ⟩
  have hmem : ∀ x : A, (a₁.prod a₂) x ∈ θ.range := by
    intro x
    obtain ⟨z, hz₁, hz₂⟩ := S.lift_loc s (a₁ x) (a₂ x) (by simpa using congrArg (· x) h)
    exact ⟨z, Prod.ext hz₁ hz₂⟩
  refine ⟨e.symm.toRingHom.comp ((a₁.prod a₂).codRestrict θ.range hmem), ?_, ?_⟩
  · ext x
    have hx : θ (e.symm ⟨(a₁.prod a₂) x, hmem x⟩) = (a₁.prod a₂) x := by
      have := e.apply_symm_apply ⟨(a₁.prod a₂) x, hmem x⟩
      exact congrArg Subtype.val this
    exact congrArg Prod.fst hx
  · ext x
    have hx : θ (e.symm ⟨(a₁.prod a₂) x, hmem x⟩) = (a₁.prod a₂) x := by
      have := e.apply_symm_apply ⟨(a₁.prod a₂) x, hmem x⟩
      exact congrArg Subtype.val this
    exact congrArg Prod.snd hx

lemma comp_eq_loc_unique {A : Type u} [CommRing A] (b b' : A →+* Localization.Away s)
    (h₁ : (ρ₁ π₁ s).comp b = (ρ₁ π₁ s).comp b') (h₂ : (ρ₂ π₂ s).comp b = (ρ₂ π₂ s).comp b') :
    b = b' := by
  ext x
  rw [← sub_eq_zero]
  refine S.inj_loc s _ ?_ ?_
  · simpa [sub_eq_zero] using congrArg (· x) h₁
  · simpa [sub_eq_zero] using congrArg (· x) h₂

end Loc

section Geometry

noncomputable abbrev iR (s : R) :
    Spec (CommRingCat.of (Localization.Away s)) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away s)))

noncomputable abbrev i₁ (π₁ : R →+* C) (s : R) :
    Spec (CommRingCat.of (Localization.Away (π₁ s))) ⟶ Spec (CommRingCat.of C) :=
  Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away (π₁ s))))

noncomputable abbrev i₂ (π₂ : R →+* C') (s : R) :
    Spec (CommRingCat.of (Localization.Away (π₂ s))) ⟶ Spec (CommRingCat.of C') :=
  Spec.map (CommRingCat.ofHom (algebraMap C' (Localization.Away (π₂ s))))

noncomputable abbrev i₀ (π₁ : R →+* C) (q : C →+* C₀) (s : R) :
    Spec (CommRingCat.of (Localization.Away (q (π₁ s)))) ⟶ Spec (CommRingCat.of C₀) :=
  Spec.map (CommRingCat.ofHom (algebraMap C₀ (Localization.Away (q (π₁ s)))))

noncomputable abbrev P₁ (π₁ : R →+* C) : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom π₁)

noncomputable abbrev P₂ (π₂ : R →+* C') : Spec (CommRingCat.of C') ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom π₂)

omit S in
lemma range_iR (s : R) :
    Set.range (iR s) = (PrimeSpectrum.basicOpen s : Set (PrimeSpectrum R)) := by
  rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away s) s]
  rfl

omit S in
lemma range_i₁ (s : R) :
    Set.range (i₁ π₁ s) = (PrimeSpectrum.basicOpen (π₁ s) : Set (PrimeSpectrum C)) := by
  rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away (π₁ s)) (π₁ s)]
  rfl

omit S in
lemma range_i₂ (s : R) :
    Set.range (i₂ π₂ s) = (PrimeSpectrum.basicOpen (π₂ s) : Set (PrimeSpectrum C')) := by
  rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away (π₂ s)) (π₂ s)]
  rfl

omit S in
lemma mem_range_iR (s : R) (y : Spec (CommRingCat.of (Localization.Away s))) :
    (iR s y : PrimeSpectrum R) ∈ PrimeSpectrum.basicOpen s := by
  have := range_iR s
  rw [Set.ext_iff] at this
  exact (this _).mp ⟨y, rfl⟩

omit S in
lemma mem_range_i₁ (s : R) (y : Spec (CommRingCat.of (Localization.Away (π₁ s)))) :
    (i₁ π₁ s y : PrimeSpectrum C) ∈ PrimeSpectrum.basicOpen (π₁ s) := by
  have := range_i₁ (π₁ := π₁) s
  rw [Set.ext_iff] at this
  exact (this _).mp ⟨y, rfl⟩

omit S in
lemma mem_range_i₂ (s : R) (y : Spec (CommRingCat.of (Localization.Away (π₂ s)))) :
    (i₂ π₂ s y : PrimeSpectrum C') ∈ PrimeSpectrum.basicOpen (π₂ s) := by
  have := range_i₂ (π₂ := π₂) s
  rw [Set.ext_iff] at this
  exact (this _).mp ⟨y, rfl⟩

omit S in

lemma spec_ρ₁_comp_iR (s : R) :
    Spec.map (CommRingCat.ofHom (ρ₁ π₁ s)) ≫ iR s = i₁ π₁ s ≫ P₁ π₁ := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact IsLocalization.map_comp _

omit S in
lemma spec_ρ₂_comp_iR (s : R) :
    Spec.map (CommRingCat.ofHom (ρ₂ π₂ s)) ≫ iR s = i₂ π₂ s ≫ P₂ π₂ := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact IsLocalization.map_comp _

omit S in
lemma spec_κ₁_comp_i₁ (s : R) :
    Spec.map (CommRingCat.ofHom (κ₁ π₁ q s)) ≫ i₁ π₁ s =
      i₀ π₁ q s ≫ Spec.map (CommRingCat.ofHom q) := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact IsLocalization.map_comp _

lemma spec_κ₂_comp_i₂ (s : R) :
    Spec.map (CommRingCat.ofHom (S.κ₂ s)) ≫ i₂ π₂ s =
      i₀ π₁ q s ≫ Spec.map (CommRingCat.ofHom q') := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact IsLocalization.map_comp _

omit S in

lemma mem_basicOpen_P₁ (s : R) (x : PrimeSpectrum C) :
    P₁ π₁ x ∈ PrimeSpectrum.basicOpen s ↔ x ∈ PrimeSpectrum.basicOpen (π₁ s) := by
  change PrimeSpectrum.comap π₁ x ∈ PrimeSpectrum.basicOpen s ↔ _
  rw [PrimeSpectrum.mem_basicOpen, PrimeSpectrum.mem_basicOpen, PrimeSpectrum.comap_asIdeal,
    Ideal.mem_comap]

omit S in
lemma mem_basicOpen_P₂ (s : R) (x : PrimeSpectrum C') :
    P₂ π₂ x ∈ PrimeSpectrum.basicOpen s ↔ x ∈ PrimeSpectrum.basicOpen (π₂ s) := by
  change PrimeSpectrum.comap π₂ x ∈ PrimeSpectrum.basicOpen s ↔ _
  rw [PrimeSpectrum.mem_basicOpen, PrimeSpectrum.mem_basicOpen, PrimeSpectrum.comap_asIdeal,
    Ideal.mem_comap]

omit S in
lemma mem_basicOpen_Q (s : R) (x : PrimeSpectrum C₀) :
    Spec.map (CommRingCat.ofHom q) x ∈ PrimeSpectrum.basicOpen (π₁ s) ↔
      x ∈ PrimeSpectrum.basicOpen (q (π₁ s)) := by
  change PrimeSpectrum.comap q x ∈ PrimeSpectrum.basicOpen (π₁ s) ↔ _
  rw [PrimeSpectrum.mem_basicOpen, PrimeSpectrum.mem_basicOpen, PrimeSpectrum.comap_asIdeal,
    Ideal.mem_comap]

omit S in
lemma mem_basicOpen_Q' (s : R) (x : PrimeSpectrum C₀) :
    Spec.map (CommRingCat.ofHom q') x ∈ PrimeSpectrum.basicOpen (π₂ s) ↔
      x ∈ PrimeSpectrum.basicOpen (q' (π₂ s)) := by
  change PrimeSpectrum.comap q' x ∈ PrimeSpectrum.basicOpen (π₂ s) ↔ _
  rw [PrimeSpectrum.mem_basicOpen, PrimeSpectrum.mem_basicOpen, PrimeSpectrum.comap_asIdeal,
    Ideal.mem_comap]

lemma surjective_P₁ : Surjective (P₁ π₁) :=
  ⟨S.bijective₁.2⟩

lemma isOpenMap_P₁ : IsOpenMap (P₁ π₁) := by
  have h : IsHomeomorph (P₁ π₁ : PrimeSpectrum C → PrimeSpectrum R) := by
    rw [isHomeomorph_iff_isEmbedding_surjective]
    exact ⟨PrimeSpectrum.isEmbedding_comap_of_surjective _ _ S.surj₁, S.bijective₁.2⟩
  exact h.isOpenMap

structure LocalDatum (π₁ : R →+* C) (π₂ : R →+* C') (X : Scheme.{u})
    (v : Spec (CommRingCat.of C) ⟶ X) (v' : Spec (CommRingCat.of C') ⟶ X) where

  s : R

  U : X.Opens
  hU : IsAffineOpen U
  h₁ : Set.range (i₁ π₁ s ≫ v) ⊆ (U : Set X)
  h₂ : Set.range (i₂ π₂ s ≫ v') ⊆ (U : Set X)

variable {X : Scheme.{u}} {v : Spec (CommRingCat.of C) ⟶ X} {v' : Spec (CommRingCat.of C') ⟶ X}

lemma range_i₂_subset (hvv' : Spec.map (CommRingCat.ofHom q) ≫ v = Spec.map (CommRingCat.ofHom q') ≫ v')
    (s : R) (U : Set X) (h₁ : Set.range (i₁ π₁ s ≫ v) ⊆ U) :
    Set.range (i₂ π₂ s ≫ v') ⊆ U := by
  rintro _ ⟨y, rfl⟩
  have hy : (i₂ π₂ s y : PrimeSpectrum C') ∈ PrimeSpectrum.basicOpen (π₂ s) := mem_range_i₂ s y
  obtain ⟨x₀, hx₀⟩ := S.bijective'.2 (i₂ π₂ s y)
  have hx₀' : Spec.map (CommRingCat.ofHom q') x₀ = i₂ π₂ s y := hx₀
  have hmem : x₀ ∈ PrimeSpectrum.basicOpen (q (π₁ s)) := by
    rw [S.w s, ← mem_basicOpen_Q', hx₀']
    exact hy
  have hmem₁ : (Spec.map (CommRingCat.ofHom q) x₀ : PrimeSpectrum C) ∈
      Set.range (i₁ π₁ s) := by
    rw [range_i₁]
    exact (mem_basicOpen_Q s x₀).mpr hmem
  obtain ⟨z, hz⟩ := hmem₁
  rw [Scheme.Hom.comp_apply, ← hx₀', ← Scheme.Hom.comp_apply, ← hvv', Scheme.Hom.comp_apply,
    ← hz, ← Scheme.Hom.comp_apply]
  exact h₁ ⟨z, rfl⟩

lemma exists_localDatum
    (hvv' : Spec.map (CommRingCat.ofHom q) ≫ v = Spec.map (CommRingCat.ofHom q') ≫ v')
    (P : Spec (CommRingCat.of R)) :
    ∃ D : LocalDatum π₁ π₂ X v v', P ∈ PrimeSpectrum.basicOpen D.s := by
  obtain ⟨x, hx⟩ := S.bijective₁.2 P
  have hx' : P₁ π₁ x = P := hx
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := v x) (U := ⊤) trivial

  set O : Set (PrimeSpectrum C) := (v ⁻¹ᵁ U : Set (Spec (CommRingCat.of C))) with hO
  have hOopen : IsOpen (P₁ π₁ '' O) := S.isOpenMap_P₁ _ (v ⁻¹ᵁ U).isOpen
  have hPO : P ∈ P₁ π₁ '' O := ⟨x, hxU, hx'⟩
  obtain ⟨_, ⟨s, rfl⟩, hPs, hsO⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hPO hOopen
  refine ⟨⟨s, U, hU, ?_, ?_⟩, hPs⟩
  · rintro _ ⟨y, rfl⟩
    have hy : P₁ π₁ (i₁ π₁ s y) ∈ PrimeSpectrum.basicOpen s :=
      (mem_basicOpen_P₁ s _).mpr (mem_range_i₁ s y)
    obtain ⟨y', hy'O, hy'⟩ := hsO hy
    have : y' = i₁ π₁ s y := S.bijective₁.1 hy'
    rw [Scheme.Hom.comp_apply, ← this]
    exact hy'O
  · refine S.range_i₂_subset hvv' s U ?_
    rintro _ ⟨y, rfl⟩
    have hy : P₁ π₁ (i₁ π₁ s y) ∈ PrimeSpectrum.basicOpen s :=
      (mem_basicOpen_P₁ s _).mpr (mem_range_i₁ s y)
    obtain ⟨y', hy'O, hy'⟩ := hsO hy
    have : y' = i₁ π₁ s y := S.bijective₁.1 hy'
    rw [Scheme.Hom.comp_apply, ← this]
    exact hy'O

namespace LocalDatum

variable (D : LocalDatum π₁ π₂ X v v')

noncomputable def a₁ : Γ(X, D.U) ⟶ CommRingCat.of (Localization.Away (π₁ D.s)) :=
  Spec.preimage (IsOpenImmersion.lift D.hU.fromSpec (i₁ π₁ D.s ≫ v)
    (by rw [D.hU.range_fromSpec]; exact D.h₁))

omit S in
lemma spec_a₁ : Spec.map D.a₁ ≫ D.hU.fromSpec = i₁ π₁ D.s ≫ v := by
  rw [a₁, Spec.map_preimage, IsOpenImmersion.lift_fac]

noncomputable def a₂ : Γ(X, D.U) ⟶ CommRingCat.of (Localization.Away (π₂ D.s)) :=
  Spec.preimage (IsOpenImmersion.lift D.hU.fromSpec (i₂ π₂ D.s ≫ v')
    (by rw [D.hU.range_fromSpec]; exact D.h₂))

omit S in
lemma spec_a₂ : Spec.map D.a₂ ≫ D.hU.fromSpec = i₂ π₂ D.s ≫ v' := by
  rw [a₂, Spec.map_preimage, IsOpenImmersion.lift_fac]

lemma compat (hvv' : Spec.map (CommRingCat.ofHom q) ≫ v = Spec.map (CommRingCat.ofHom q') ≫ v') :
    (κ₁ π₁ q D.s).comp D.a₁.hom = (S.κ₂ D.s).comp D.a₂.hom := by
  have : D.a₁ ≫ CommRingCat.ofHom (κ₁ π₁ q D.s) = D.a₂ ≫ CommRingCat.ofHom (S.κ₂ D.s) := by
    apply Spec.map_injective
    rw [← cancel_mono D.hU.fromSpec]
    simp only [Spec.map_comp, Category.assoc, spec_a₁, spec_a₂]
    rw [reassoc_of% (spec_κ₁_comp_i₁ (π₁ := π₁) (q := q) D.s),
      reassoc_of% (S.spec_κ₂_comp_i₂ D.s), hvv']
  exact congrArg CommRingCat.Hom.hom this

noncomputable def b (hvv' : Spec.map (CommRingCat.ofHom q) ≫ v = Spec.map (CommRingCat.ofHom q') ≫ v') :
    Γ(X, D.U) →+* Localization.Away D.s :=
  (S.exists_comp_eq_loc D.s D.a₁.hom D.a₂.hom (D.compat S hvv')).choose

lemma ρ₁_comp_b (hvv' : Spec.map (CommRingCat.ofHom q) ≫ v = Spec.map (CommRingCat.ofHom q') ≫ v') :
    (ρ₁ π₁ D.s).comp (D.b S hvv') = D.a₁.hom :=
  (S.exists_comp_eq_loc D.s D.a₁.hom D.a₂.hom (D.compat S hvv')).choose_spec.1

lemma ρ₂_comp_b (hvv' : Spec.map (CommRingCat.ofHom q) ≫ v = Spec.map (CommRingCat.ofHom q') ≫ v') :
    (ρ₂ π₂ D.s).comp (D.b S hvv') = D.a₂.hom :=
  (S.exists_comp_eq_loc D.s D.a₁.hom D.a₂.hom (D.compat S hvv')).choose_spec.2

noncomputable def wloc
    (hvv' : Spec.map (CommRingCat.ofHom q) ≫ v = Spec.map (CommRingCat.ofHom q') ≫ v') :
    Spec (CommRingCat.of (Localization.Away D.s)) ⟶ X :=
  Spec.map (CommRingCat.ofHom (D.b S hvv')) ≫ D.hU.fromSpec

lemma spec_ρ₁_comp_wloc
    (hvv' : Spec.map (CommRingCat.ofHom q) ≫ v = Spec.map (CommRingCat.ofHom q') ≫ v') :
    Spec.map (CommRingCat.ofHom (ρ₁ π₁ D.s)) ≫ D.wloc S hvv' = i₁ π₁ D.s ≫ v := by
  rw [wloc, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, D.ρ₁_comp_b S hvv',
    CommRingCat.ofHom_hom, spec_a₁]

lemma spec_ρ₂_comp_wloc
    (hvv' : Spec.map (CommRingCat.ofHom q) ≫ v = Spec.map (CommRingCat.ofHom q') ≫ v') :
    Spec.map (CommRingCat.ofHom (ρ₂ π₂ D.s)) ≫ D.wloc S hvv' = i₂ π₂ D.s ≫ v' := by
  rw [wloc, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, D.ρ₂_comp_b S hvv',
    CommRingCat.ofHom_hom, spec_a₂]

lemma comp_wloc_eq₁
    (hvv' : Spec.map (CommRingCat.ofHom q) ≫ v = Spec.map (CommRingCat.ofHom q') ≫ v')
    {W : Scheme.{u}} (g : W ⟶ Spec (CommRingCat.of (Localization.Away D.s)))
    (h : W ⟶ Spec (CommRingCat.of C)) (hgh : g ≫ iR D.s = h ≫ P₁ π₁) :
    g ≫ D.wloc S hvv' = h ≫ v := by
  have hrange : Set.range h ⊆ Set.range (i₁ π₁ D.s) := by
    rintro _ ⟨y, rfl⟩
    rw [range_i₁]
    have : P₁ π₁ (h y) ∈ PrimeSpectrum.basicOpen D.s := by
      rw [← Scheme.Hom.comp_apply, ← hgh, Scheme.Hom.comp_apply]
      exact mem_range_iR D.s (g y)
    exact (mem_basicOpen_P₁ D.s (h y)).mp this
  set hc := IsOpenImmersion.lift (i₁ π₁ D.s) h hrange with hhc
  have hc_fac : hc ≫ i₁ π₁ D.s = h := IsOpenImmersion.lift_fac _ _ _
  have hg : g = hc ≫ Spec.map (CommRingCat.ofHom (ρ₁ π₁ D.s)) := by
    rw [← cancel_mono (iR D.s), Category.assoc, spec_ρ₁_comp_iR, ← Category.assoc, hc_fac, hgh]
  rw [hg, Category.assoc, D.spec_ρ₁_comp_wloc S hvv', ← Category.assoc, hc_fac]

lemma comp_wloc_eq₂
    (hvv' : Spec.map (CommRingCat.ofHom q) ≫ v = Spec.map (CommRingCat.ofHom q') ≫ v')
    {W : Scheme.{u}} (g : W ⟶ Spec (CommRingCat.of (Localization.Away D.s)))
    (h : W ⟶ Spec (CommRingCat.of C')) (hgh : g ≫ iR D.s = h ≫ P₂ π₂) :
    g ≫ D.wloc S hvv' = h ≫ v' := by
  have hrange : Set.range h ⊆ Set.range (i₂ π₂ D.s) := by
    rintro _ ⟨y, rfl⟩
    rw [range_i₂]
    have : P₂ π₂ (h y) ∈ PrimeSpectrum.basicOpen D.s := by
      rw [← Scheme.Hom.comp_apply, ← hgh, Scheme.Hom.comp_apply]
      exact mem_range_iR D.s (g y)
    exact (mem_basicOpen_P₂ D.s (h y)).mp this
  set hc := IsOpenImmersion.lift (i₂ π₂ D.s) h hrange with hhc
  have hc_fac : hc ≫ i₂ π₂ D.s = h := IsOpenImmersion.lift_fac _ _ _
  have hg : g = hc ≫ Spec.map (CommRingCat.ofHom (ρ₂ π₂ D.s)) := by
    rw [← cancel_mono (iR D.s), Category.assoc, spec_ρ₂_comp_iR, ← Category.assoc, hc_fac, hgh]
  rw [hg, Category.assoc, D.spec_ρ₂_comp_wloc S hvv', ← Category.assoc, hc_fac]

end LocalDatum

lemma hom_ext_thick {W : Scheme.{u}} (j : W ⟶ Spec (CommRingCat.of R)) [IsOpenImmersion j]
    (w₁ w₂ : W ⟶ X)
    (H₁ : ∀ ⦃W' : Scheme.{u}⦄ (g : W' ⟶ W) (h : W' ⟶ Spec (CommRingCat.of C)),
      g ≫ j = h ≫ P₁ π₁ → g ≫ w₁ = g ≫ w₂)
    (H₂ : ∀ ⦃W' : Scheme.{u}⦄ (g : W' ⟶ W) (h : W' ⟶ Spec (CommRingCat.of C')),
      g ≫ j = h ≫ P₂ π₂ → g ≫ w₁ = g ≫ w₂) :
    w₁ = w₂ := by
  haveI := S.surjective_P₁
  apply Scheme.hom_ext_of_forall
  intro p

  have hbase : w₁ p = w₂ p := by
    obtain ⟨p', rfl⟩ := (pullback.fst j (P₁ π₁)).surjective p
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
      H₁ (pullback.fst j (P₁ π₁)) (pullback.snd j (P₁ π₁)) pullback.condition]

  obtain ⟨U, hU, hpU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := w₁ p) (U := ⊤) trivial
  set O : W.Opens := w₁ ⁻¹ᵁ U ⊓ w₂ ⁻¹ᵁ U with hO
  have hpO : p ∈ O := ⟨hpU, show w₂ p ∈ U by rwa [← hbase]⟩
  have hOopen : IsOpen (j '' (O : Set W)) := j.isOpenEmbedding.isOpenMap _ O.isOpen
  have hpO' : j p ∈ j '' (O : Set W) := ⟨p, hpO, rfl⟩
  obtain ⟨_, ⟨s, rfl⟩, hps, hsO⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hpO' hOopen

  have hrange : Set.range (iR s) ⊆ Set.range j := by
    rw [range_iR]
    exact hsO.trans (Set.image_subset_range _ _)
  set ℓ := IsOpenImmersion.lift j (iR s) hrange with hℓ
  have hℓj : ℓ ≫ j = iR s := IsOpenImmersion.lift_fac _ _ _
  have hℓO : Set.range ℓ ⊆ (O : Set W) := by
    rintro _ ⟨y, rfl⟩
    have : j (ℓ y) ∈ j '' (O : Set W) := by
      apply hsO
      rw [← Scheme.Hom.comp_apply, hℓj]
      exact mem_range_iR s y
    obtain ⟨o, ho, hoe⟩ := this
    rwa [← j.isOpenEmbedding.injective hoe]
  have hpℓ : p ∈ ℓ.opensRange := by
    have : j p ∈ Set.range (iR s) := by rw [range_iR]; exact hps
    obtain ⟨y, hy⟩ := this
    rw [← hℓj, Scheme.Hom.comp_apply] at hy
    exact ⟨y, j.isOpenEmbedding.injective hy⟩
  refine ⟨ℓ.opensRange, hpℓ, ?_⟩
  rw [← cancel_epi ℓ.isoOpensRange.hom, ℓ.isoOpensRange_hom_ι_assoc, ℓ.isoOpensRange_hom_ι_assoc]

  have hr₁ : Set.range (ℓ ≫ w₁) ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro _ ⟨y, rfl⟩
    exact (hℓO ⟨y, rfl⟩).1
  have hr₂ : Set.range (ℓ ≫ w₂) ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro _ ⟨y, rfl⟩
    exact (hℓO ⟨y, rfl⟩).2
  set φ₁ := Spec.preimage (IsOpenImmersion.lift hU.fromSpec (ℓ ≫ w₁) hr₁) with hφ₁'
  set φ₂ := Spec.preimage (IsOpenImmersion.lift hU.fromSpec (ℓ ≫ w₂) hr₂) with hφ₂'
  have hφ₁ : Spec.map φ₁ ≫ hU.fromSpec = ℓ ≫ w₁ := by
    rw [hφ₁', Spec.map_preimage, IsOpenImmersion.lift_fac]
  have hφ₂ : Spec.map φ₂ ≫ hU.fromSpec = ℓ ≫ w₂ := by
    rw [hφ₂', Spec.map_preimage, IsOpenImmersion.lift_fac]
  rw [← hφ₁, ← hφ₂]
  suffices hφ : φ₁ = φ₂ by rw [hφ]
  apply CommRingCat.hom_ext
  refine S.comp_eq_loc_unique s φ₁.hom φ₂.hom ?_ ?_
  · have : φ₁ ≫ CommRingCat.ofHom (ρ₁ π₁ s) = φ₂ ≫ CommRingCat.ofHom (ρ₁ π₁ s) := by
      apply Spec.map_injective
      rw [← cancel_mono hU.fromSpec]
      simp only [Spec.map_comp, Category.assoc, hφ₁, hφ₂]
      simpa only [Category.assoc] using
        H₁ (Spec.map (CommRingCat.ofHom (ρ₁ π₁ s)) ≫ ℓ) (i₁ π₁ s)
          (by rw [Category.assoc, hℓj, spec_ρ₁_comp_iR])
    exact congrArg CommRingCat.Hom.hom this
  · have : φ₁ ≫ CommRingCat.ofHom (ρ₂ π₂ s) = φ₂ ≫ CommRingCat.ofHom (ρ₂ π₂ s) := by
      apply Spec.map_injective
      rw [← cancel_mono hU.fromSpec]
      simp only [Spec.map_comp, Category.assoc, hφ₁, hφ₂]
      simpa only [Category.assoc] using
        H₂ (Spec.map (CommRingCat.ofHom (ρ₂ π₂ s)) ≫ ℓ) (i₂ π₂ s)
          (by rw [Category.assoc, hℓj, spec_ρ₂_comp_iR])
    exact congrArg CommRingCat.Hom.hom this

section Glue

variable (hvv' : Spec.map (CommRingCat.ofHom q) ≫ v = Spec.map (CommRingCat.ofHom q') ≫ v')
include hvv'

noncomputable def datum (P : Spec (CommRingCat.of R)) : LocalDatum π₁ π₂ X v v' :=
  (S.exists_localDatum hvv' P).choose

lemma mem_datum (P : Spec (CommRingCat.of R)) :
    P ∈ PrimeSpectrum.basicOpen (S.datum hvv' P).s :=
  (S.exists_localDatum hvv' P).choose_spec

lemma span_datum :
    Ideal.span (Set.range fun P : Spec (CommRingCat.of R) => (S.datum hvv' P).s) = ⊤ := by
  rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff]
  refine top_le_iff.mp fun P _ => ?_
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨P, S.mem_datum hvv' P⟩

noncomputable def cover : (Spec (CommRingCat.of R)).OpenCover :=
  (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of R)
    (fun P : Spec (CommRingCat.of R) => (S.datum hvv' P).s) (S.span_datum hvv')).openCover

lemma cover_f (P : Spec (CommRingCat.of R)) : (S.cover hvv').f P = iR (S.datum hvv' P).s := rfl

lemma glue_compat (P Q : Spec (CommRingCat.of R)) :
    pullback.fst ((S.cover hvv').f P) ((S.cover hvv').f Q) ≫ (S.datum hvv' P).wloc S hvv' =
      pullback.snd ((S.cover hvv').f P) ((S.cover hvv').f Q) ≫ (S.datum hvv' Q).wloc S hvv' := by
  refine S.hom_ext_thick (pullback.fst _ _ ≫ (S.cover hvv').f P) _ _ ?_ ?_
  · intro W' g h hgh
    have hg₁ : (g ≫ pullback.fst ((S.cover hvv').f P) ((S.cover hvv').f Q)) ≫
        iR (S.datum hvv' P).s = h ≫ P₁ π₁ := by
      rw [Category.assoc]; exact hgh
    have hg₂ : (g ≫ pullback.snd ((S.cover hvv').f P) ((S.cover hvv').f Q)) ≫
        iR (S.datum hvv' Q).s = h ≫ P₁ π₁ := by
      rw [Category.assoc, ← S.cover_f hvv' Q, ← pullback.condition]; exact hgh
    have e₁ := (S.datum hvv' P).comp_wloc_eq₁ S hvv' _ h hg₁
    have e₂ := (S.datum hvv' Q).comp_wloc_eq₁ S hvv' _ h hg₂
    exact (Category.assoc _ _ _).symm.trans (e₁.trans (e₂.symm.trans (Category.assoc _ _ _)))
  · intro W' g h hgh
    have hg₁ : (g ≫ pullback.fst ((S.cover hvv').f P) ((S.cover hvv').f Q)) ≫
        iR (S.datum hvv' P).s = h ≫ P₂ π₂ := by
      rw [Category.assoc]; exact hgh
    have hg₂ : (g ≫ pullback.snd ((S.cover hvv').f P) ((S.cover hvv').f Q)) ≫
        iR (S.datum hvv' Q).s = h ≫ P₂ π₂ := by
      rw [Category.assoc, ← S.cover_f hvv' Q, ← pullback.condition]; exact hgh
    have e₁ := (S.datum hvv' P).comp_wloc_eq₂ S hvv' _ h hg₁
    have e₂ := (S.datum hvv' Q).comp_wloc_eq₂ S hvv' _ h hg₂
    exact (Category.assoc _ _ _).symm.trans (e₁.trans (e₂.symm.trans (Category.assoc _ _ _)))

noncomputable def desc : Spec (CommRingCat.of R) ⟶ X :=
  (S.cover hvv').glueMorphisms (fun P => (S.datum hvv' P).wloc S hvv') (S.glue_compat hvv')

lemma cover_f_desc (P : Spec (CommRingCat.of R)) :
    iR (S.datum hvv' P).s ≫ S.desc hvv' = (S.datum hvv' P).wloc S hvv' :=
  Scheme.Cover.ι_glueMorphisms (S.cover hvv') _ _ P

lemma P₁_desc : P₁ π₁ ≫ S.desc hvv' = v := by
  have hspan : Ideal.span
      (Set.range fun P : Spec (CommRingCat.of R) => π₁ (S.datum hvv' P).s) = ⊤ := by
    rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff]
    refine top_le_iff.mp fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨P₁ π₁ x, ?_⟩
    exact (mem_basicOpen_P₁ _ x).mp (S.mem_datum hvv' _)
  refine Scheme.Cover.hom_ext
    (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of C) _ hspan).openCover _ _
    fun P => ?_
  change i₁ π₁ (S.datum hvv' P).s ≫ P₁ π₁ ≫ S.desc hvv' = i₁ π₁ (S.datum hvv' P).s ≫ v
  rw [← reassoc_of% (spec_ρ₁_comp_iR (π₁ := π₁) (S.datum hvv' P).s), S.cover_f_desc hvv',
    LocalDatum.spec_ρ₁_comp_wloc]

lemma P₂_desc : P₂ π₂ ≫ S.desc hvv' = v' := by
  have hspan : Ideal.span
      (Set.range fun P : Spec (CommRingCat.of R) => π₂ (S.datum hvv' P).s) = ⊤ := by
    rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff]
    refine top_le_iff.mp fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨P₂ π₂ x, ?_⟩
    exact (mem_basicOpen_P₂ _ x).mp (S.mem_datum hvv' _)
  refine Scheme.Cover.hom_ext
    (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of C') _ hspan).openCover _ _
    fun P => ?_
  change i₂ π₂ (S.datum hvv' P).s ≫ P₂ π₂ ≫ S.desc hvv' = i₂ π₂ (S.datum hvv' P).s ≫ v'
  rw [← reassoc_of% (spec_ρ₂_comp_iR (π₂ := π₂) (S.datum hvv' P).s), S.cover_f_desc hvv',
    LocalDatum.spec_ρ₂_comp_wloc]

lemma desc_unique (m : Spec (CommRingCat.of R) ⟶ X) (h₁ : P₁ π₁ ≫ m = v) (h₂ : P₂ π₂ ≫ m = v') :
    m = S.desc hvv' := by
  refine S.hom_ext_thick (𝟙 _) _ _ ?_ ?_
  · intro W' g h hgh
    rw [Category.comp_id] at hgh
    rw [hgh, Category.assoc, Category.assoc, h₁, S.P₁_desc hvv']
  · intro W' g h hgh
    rw [Category.comp_id] at hgh
    rw [hgh, Category.assoc, Category.assoc, h₂, S.P₂_desc hvv']

end Glue

omit v v' in
theorem isPushout :
    IsPushout (Spec.map (CommRingCat.ofHom q)) (Spec.map (CommRingCat.ofHom q'))
      (P₁ π₁) (P₂ π₂) := by
  have w : Spec.map (CommRingCat.ofHom q) ≫ P₁ π₁ = Spec.map (CommRingCat.ofHom q') ≫ P₂ π₂ := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext S.w
  refine IsPushout.of_isColimit' ⟨w⟩ (PushoutCocone.IsColimit.mk w
    (fun c => S.desc (X := c.pt) (v := c.inl) (v' := c.inr) c.condition)
    (fun c => S.P₁_desc c.condition) (fun c => S.P₂_desc c.condition)
    (fun c m h₁ h₂ => S.desc_unique c.condition m h₁ h₂))

end Geometry

end Setup

end P2mThickeningPushout

open P2mThickeningPushout in
theorem solution
    {R C C' C₀ : CommRingCat.{u}} {fst : R ⟶ C} {snd : R ⟶ C'} {q : C ⟶ C₀} {q' : C' ⟶ C₀}
    (H : IsPullback fst snd q q') (hq' : Function.Surjective q'.hom)
    (hnil : ∀ x ∈ RingHom.ker q'.hom, IsNilpotent x) :
    IsPushout (Spec.map q) (Spec.map q') (Spec.map fst) (Spec.map snd) := by

  have hc : IsPullback (CommRingCat.pullbackCone q q').fst (CommRingCat.pullbackCone q q').snd q q' :=
    IsPullback.of_isLimit (CommRingCat.pullbackConeIsLimit q q')
  let e : R ≅ (CommRingCat.pullbackCone q q').pt := H.isoIsPullback _ _ hc
  have he₁ : ∀ r : R, (e.hom r).1.1 = fst r := fun r =>
    congrArg (fun f : R ⟶ C => f r) (H.isoIsPullback_hom_fst _ _ hc)
  have he₂ : ∀ r : R, (e.hom r).1.2 = snd r := fun r =>
    congrArg (fun f : R ⟶ C' => f r) (H.isoIsPullback_hom_snd _ _ hc)
  have S : Setup fst.hom snd.hom q.hom q'.hom :=
    { w := fun r => congrArg (fun f : R ⟶ C₀ => f r) H.w
      inj := fun x y h₁ h₂ => by
        apply e.commRingCatIsoToRingEquiv.injective
        change e.hom x = e.hom y
        refine Subtype.ext (Prod.ext ?_ ?_)
        · rw [he₁, he₁]; exact h₁
        · rw [he₂, he₂]; exact h₂
      lift := fun c c' h => by
        refine ⟨e.inv ⟨(c, c'), h⟩, ?_, ?_⟩
        · change (e.inv ≫ fst) _ = c
          rw [H.isoIsPullback_inv_fst _ _ hc]
          rfl
        · change (e.inv ≫ snd) _ = c'
          rw [H.isoIsPullback_inv_snd _ _ hc]
          rfl
      surj := hq'
      nil := fun x hx => hnil x hx }
  exact S.isPushout

end S_AlgebraicGeometry_isPushout_specMap_of_isPullback_of_surjective_of_isNilpotent
end P2MW
export P2MW.S_AlgebraicGeometry_isPushout_specMap_of_isPullback_of_surjective_of_isNilpotent (solution)
