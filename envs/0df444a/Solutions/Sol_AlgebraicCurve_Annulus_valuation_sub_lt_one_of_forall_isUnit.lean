-- Prove2me | solution 1 for AlgebraicCurve.Annulus.valuation_sub_lt_one_of_forall_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/41895494-093e-5b0e-b5ea-703410ade659

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Annulus_valuation_sub_lt_one_of_forall_isUnit

set_option autoImplicit false

open AlgebraicCurve IsLocalRing
open scoped WithZero

namespace AF8ConstRed

section Engine

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {ι : Type*}

def levN (vc : Γ₀) (k : ℤ) (Z : Finset ι) (lv : ι → Γ₀) (d : ι → ℕ) (σ : Γ₀) : Γ₀ :=
  vc * σ ^ k * ∏ P ∈ Z, (max σ (lv P)) ^ d P

def wle (Z : Finset ι) (lv : ι → Γ₀) (d : ι → ℕ) (τ : Γ₀) : ℕ :=
  ∑ P ∈ Z.filter (fun P => lv P ≤ τ), d P

def wlt (Z : Finset ι) (lv : ι → Γ₀) (d : ι → ℕ) (τ : Γ₀) : ℕ :=
  ∑ P ∈ Z.filter (fun P => lv P < τ), d P

def weq (Z : Finset ι) (lv : ι → Γ₀) (d : ι → ℕ) (τ : Γ₀) : ℕ :=
  ∑ P ∈ Z.filter (fun P => lv P = τ), d P

theorem wle_eq_wlt_add_weq (Z : Finset ι) (lv : ι → Γ₀) (d : ι → ℕ) (τ : Γ₀) :
    wle Z lv d τ = wlt Z lv d τ + weq Z lv d τ := by
  classical
  unfold wle wlt weq
  rw [← Finset.sum_union]
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext P
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hP, hle⟩
      rcases lt_or_eq_of_le hle with h | h
      · exact Or.inl ⟨hP, h⟩
      · exact Or.inr ⟨hP, h⟩
    · rintro (⟨hP, h⟩ | ⟨hP, h⟩)
      · exact ⟨hP, le_of_lt h⟩
      · exact ⟨hP, le_of_eq h⟩
  · rw [Finset.disjoint_filter]
    intro P _ h1 h2
    exact (ne_of_lt h1) h2

theorem le_weq_of_mem (Z : Finset ι) (lv : ι → Γ₀) (d : ι → ℕ) {P : ι} (hP : P ∈ Z) :
    d P ≤ weq Z lv d (lv P) := by
  classical
  unfold weq
  exact Finset.single_le_sum (f := d) (fun _ _ => Nat.zero_le _)
    (Finset.mem_filter.mpr ⟨hP, rfl⟩)

theorem levN_eq_mul_zpow (vc : Γ₀) (k : ℤ) (Z : Finset ι) (lv : ι → Γ₀) (d : ι → ℕ)
    {τ σ : Γ₀} (hτ : τ ≠ 0) (hle : τ ≤ σ)
    (hgap : ∀ P ∈ Z, lv P ≤ τ ∨ σ ≤ lv P) :
    levN vc k Z lv d σ = levN vc k Z lv d τ * (σ * τ⁻¹) ^ (k + (wle Z lv d τ : ℤ)) := by
  classical
  have hσ : σ ≠ 0 := fun h => hτ (le_antisymm (h ▸ hle) (zero_le'))
  unfold levN wle
  set S := Z.filter (fun P => lv P ≤ τ) with hS
  set n : ℕ := ∑ P ∈ S, d P with hn

  have hprodσ : ∏ P ∈ Z, (max σ (lv P)) ^ d P =
      σ ^ n * ∏ P ∈ Z.filter (fun P => ¬ lv P ≤ τ), (lv P) ^ d P := by
    rw [← Finset.prod_filter_mul_prod_filter_not Z (fun P => lv P ≤ τ)]
    congr 1
    · rw [hn, ← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_congr rfl fun P hP => ?_
      rw [Finset.mem_filter] at hP
      rw [max_eq_left (hP.2.trans hle)]
    · refine Finset.prod_congr rfl fun P hP => ?_
      rw [Finset.mem_filter] at hP
      rcases hgap P hP.1 with h | h
      · exact absurd h hP.2
      · rw [max_eq_right h]
  have hprodτ : ∏ P ∈ Z, (max τ (lv P)) ^ d P =
      τ ^ n * ∏ P ∈ Z.filter (fun P => ¬ lv P ≤ τ), (lv P) ^ d P := by
    rw [← Finset.prod_filter_mul_prod_filter_not Z (fun P => lv P ≤ τ)]
    congr 1
    · rw [hn, ← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_congr rfl fun P hP => ?_
      rw [Finset.mem_filter] at hP
      rw [max_eq_left hP.2]
    · refine Finset.prod_congr rfl fun P hP => ?_
      rw [Finset.mem_filter] at hP
      rw [max_eq_right (le_of_lt (not_le.mp hP.2))]
  rw [hprodσ, hprodτ]
  set R := ∏ P ∈ Z.filter (fun P => ¬ lv P ≤ τ), (lv P) ^ d P
  rw [zpow_add₀ (mul_ne_zero hσ (inv_ne_zero hτ)), zpow_natCast, mul_zpow, mul_pow, inv_zpow, inv_pow]
  have h1 : τ ^ k * (τ ^ k)⁻¹ = 1 := mul_inv_cancel₀ (zpow_ne_zero k hτ)
  have h2 : τ ^ n * (τ ^ n)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero n hτ)
  calc vc * σ ^ k * (σ ^ n * R)
      = vc * σ ^ k * (σ ^ n * R) * (τ ^ k * (τ ^ k)⁻¹) * (τ ^ n * (τ ^ n)⁻¹) := by rw [h1, h2, mul_one, mul_one]
    _ = vc * τ ^ k * (τ ^ n * R) * (σ ^ k * (τ ^ k)⁻¹ * (σ ^ n * (τ ^ n)⁻¹)) := by ac_rfl

theorem exists_between_of_sq (Hsq : ∀ x : Γ₀, ∃ s, s * s = x) {α β : Γ₀} (h : α < β) (hα : α ≠ 0) :
    ∃ σ, α < σ ∧ σ < β := by
  obtain ⟨s, hs⟩ := Hsq (α * β)
  have hα0 : 0 < α := lt_of_le_of_ne (zero_le') (Ne.symm hα)
  have hβ0 : 0 < β := lt_trans hα0 h
  refine ⟨s, ?_, ?_⟩
  · by_contra hle
    push Not at hle
    have h1 : s * s ≤ α * α := mul_le_mul' hle hle
    have h2 : α * α < α * β := mul_lt_mul_of_pos_left h hα0
    rw [hs] at h1
    exact absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)
  · by_contra hle
    push Not at hle
    have h1 : β * β ≤ s * s := mul_le_mul' hle hle
    have h2 : α * β < β * β := mul_lt_mul_of_pos_right h hβ0
    rw [hs] at h1
    exact absurd (lt_of_lt_of_le h2 h1) (lt_irrefl _)

theorem exists_between_zero {β : Γ₀} (h0 : 0 < β) (h1 : β < 1) : ∃ σ, 0 < σ ∧ σ < β := by
  refine ⟨β * β, mul_pos h0 h0, ?_⟩
  calc β * β < β * 1 := mul_lt_mul_of_pos_left h1 h0
    _ = β := mul_one β

theorem exps_of_one_le_levN (vc : Γ₀) (k : ℤ) (Z : Finset ι) (lv : ι → Γ₀) (d : ι → ℕ) (lo : Γ₀)
    (Hsq : ∀ x : Γ₀, ∃ s, s * s = x)
    (Hgen : ∀ σ, lo < σ → σ < 1 → σ ≠ 0 → (∀ P ∈ Z, lv P ≠ σ) → levN vc k Z lv d σ ≤ 1)
    {lam : Γ₀} (h1 : lo < lam) (h2 : lam < 1) (h0 : lam ≠ 0)
    (hN : 1 ≤ levN vc k Z lv d lam) :
    k + (wle Z lv d lam : ℤ) ≤ 0 ∧ 0 ≤ k + (wlt Z lv d lam : ℤ) := by
  classical
  have hlam0 : 0 < lam := lt_of_le_of_ne (zero_le') (Ne.symm h0)
  have hNpos : 0 < levN vc k Z lv d lam := lt_of_lt_of_le zero_lt_one hN
  constructor
  ·
    set S : Finset Γ₀ := insert 1 ((Z.filter (fun P => lam < lv P)).image lv) with hS
    have hSne : S.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
    set β := S.min' hSne with hβ
    have hβle1 : β ≤ 1 := Finset.min'_le S 1 (Finset.mem_insert_self _ _)
    have hlamβ : lam < β := by
      rw [hβ, Finset.lt_min'_iff]
      intro y hy
      rw [hS, Finset.mem_insert, Finset.mem_image] at hy
      rcases hy with rfl | ⟨P, hP, rfl⟩
      · exact h2
      · exact (Finset.mem_filter.mp hP).2
    have hβmin : ∀ P ∈ Z, lam < lv P → β ≤ lv P := fun P hP hlt =>
      Finset.min'_le S _ (by
        rw [hS, Finset.mem_insert, Finset.mem_image]
        exact Or.inr ⟨P, Finset.mem_filter.mpr ⟨hP, hlt⟩, rfl⟩)
    obtain ⟨μ, hlamμ, hμβ⟩ := exists_between_of_sq Hsq hlamβ h0
    have hμ0 : μ ≠ 0 := ne_of_gt (lt_trans hlam0 hlamμ)
    have hμ1 : μ < 1 := lt_of_lt_of_le hμβ hβle1
    have hloμ : lo < μ := lt_trans h1 hlamμ
    have hμgen : ∀ P ∈ Z, lv P ≠ μ := by
      intro P hP heq
      by_cases hlt : lam < lv P
      · exact absurd (heq ▸ hβmin P hP hlt) (not_le.mpr hμβ)
      · exact hlt (heq ▸ hlamμ)
    have hgap : ∀ P ∈ Z, lv P ≤ lam ∨ μ ≤ lv P := by
      intro P hP
      by_cases hlt : lam < lv P
      · exact Or.inr (le_trans (le_of_lt hμβ) (hβmin P hP hlt))
      · exact Or.inl (not_lt.mp hlt)
    have hC := levN_eq_mul_zpow vc k Z lv d h0 (le_of_lt hlamμ) hgap
    have hle1 : levN vc k Z lv d μ ≤ 1 := Hgen μ hloμ hμ1 hμ0 hμgen
    have hbase : 1 < μ * lam⁻¹ := by
      rw [lt_mul_inv_iff₀ hlam0, one_mul]; exact hlamμ
    by_contra hpos
    push Not at hpos
    have hgt : 1 < (μ * lam⁻¹) ^ (k + (wle Z lv d lam : ℤ)) := (one_lt_zpow_iff_right₀ hbase).mpr hpos
    have : levN vc k Z lv d lam * 1 < levN vc k Z lv d lam * (μ * lam⁻¹) ^ (k + (wle Z lv d lam : ℤ)) :=
      mul_lt_mul_of_pos_left hgt hNpos
    rw [mul_one, ← hC] at this
    exact absurd (lt_of_lt_of_le (lt_of_le_of_lt hN this) hle1) (lt_irrefl _)
  ·
    set S : Finset Γ₀ := insert lo ((Z.filter (fun P => lv P < lam)).image lv) with hS
    have hSne : S.Nonempty := ⟨lo, Finset.mem_insert_self _ _⟩
    set α := S.max' hSne with hα
    have hloα : lo ≤ α := Finset.le_max' S lo (Finset.mem_insert_self _ _)
    have hαlam : α < lam := by
      rw [hα, Finset.max'_lt_iff]
      intro y hy
      rw [hS, Finset.mem_insert, Finset.mem_image] at hy
      rcases hy with rfl | ⟨P, hP, rfl⟩
      · exact h1
      · exact (Finset.mem_filter.mp hP).2
    have hαmax : ∀ P ∈ Z, lv P < lam → lv P ≤ α := fun P hP hlt =>
      Finset.le_max' S _ (by
        rw [hS, Finset.mem_insert, Finset.mem_image]
        exact Or.inr ⟨P, Finset.mem_filter.mpr ⟨hP, hlt⟩, rfl⟩)

    have hμex : ∃ μ, α < μ ∧ μ < lam ∧ μ ≠ 0 := by
      by_cases hα0 : α = 0
      · obtain ⟨μ, hμ0, hμlam⟩ := exists_between_zero hlam0 h2
        exact ⟨μ, hα0 ▸ hμ0, hμlam, ne_of_gt hμ0⟩
      · obtain ⟨μ, hαμ, hμlam⟩ := exists_between_of_sq Hsq hαlam hα0
        exact ⟨μ, hαμ, hμlam, ne_of_gt (lt_of_le_of_lt (zero_le') hαμ)⟩
    obtain ⟨μ, hαμ, hμlam, hμ0⟩ := hμex
    have hμpos : 0 < μ := lt_of_le_of_ne (zero_le') (Ne.symm hμ0)
    have hμ1 : μ < 1 := lt_trans hμlam h2
    have hloμ : lo < μ := lt_of_le_of_lt hloα hαμ
    have hμgen : ∀ P ∈ Z, lv P ≠ μ := by
      intro P hP heq
      by_cases hlt : lv P < lam
      · exact absurd (heq ▸ hαmax P hP hlt) (not_le.mpr hαμ)
      · exact hlt (heq ▸ hμlam)
    have hgap : ∀ P ∈ Z, lv P ≤ μ ∨ lam ≤ lv P := by
      intro P hP
      by_cases hlt : lv P < lam
      · exact Or.inl (le_trans (hαmax P hP hlt) (le_of_lt hαμ))
      · exact Or.inr (not_lt.mp hlt)
    have hC := levN_eq_mul_zpow vc k Z lv d hμ0 (le_of_lt hμlam) hgap
    have hle1 : levN vc k Z lv d μ ≤ 1 := Hgen μ hloμ hμ1 hμ0 hμgen

    have hw : wle Z lv d μ = wlt Z lv d lam := by
      unfold wle wlt
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext P
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hP, hle⟩; exact ⟨hP, lt_of_le_of_lt hle hμlam⟩
      · rintro ⟨hP, hlt⟩; exact ⟨hP, le_trans (hαmax P hP hlt) (le_of_lt hαμ)⟩
    rw [hw] at hC
    have hbase : 1 < lam * μ⁻¹ := by
      rw [lt_mul_inv_iff₀ hμpos, one_mul]; exact hμlam
    by_contra hneg
    push Not at hneg
    have hlt1 : (lam * μ⁻¹) ^ (k + (wlt Z lv d lam : ℤ)) < 1 := by
      have := (one_le_zpow_iff_right₀ hbase (n := k + (wlt Z lv d lam : ℤ))).not.mpr (not_le.mpr hneg)
      exact not_le.mp this
    have : levN vc k Z lv d μ * (lam * μ⁻¹) ^ (k + (wlt Z lv d lam : ℤ)) ≤
        1 * (lam * μ⁻¹) ^ (k + (wlt Z lv d lam : ℤ)) := mul_le_mul_left hle1 _
    rw [← hC, one_mul] at this
    exact absurd (lt_of_le_of_lt (le_trans hN this) hlt1) (lt_irrefl _)

theorem false_of_one_le_levN (vc : Γ₀) (k : ℤ) (Z : Finset ι) (lv : ι → Γ₀) (d : ι → ℕ) (lo : Γ₀)
    (hd : ∀ P ∈ Z, 0 < d P) (hZ : Z.Nonempty)
    (Hlv : ∀ P ∈ Z, lo < lv P ∧ lv P < 1)
    (Hsq : ∀ x : Γ₀, ∃ s, s * s = x)
    (Hgen : ∀ σ, lo < σ → σ < 1 → σ ≠ 0 → (∀ P ∈ Z, lv P ≠ σ) → levN vc k Z lv d σ ≤ 1)
    {lam : Γ₀} (h1 : lo < lam) (h2 : lam < 1) (h0 : lam ≠ 0)
    (hN : 1 ≤ levN vc k Z lv d lam) : False := by
  classical
  have Hlv0 : ∀ P ∈ Z, lv P ≠ 0 := fun P hP => ne_of_gt (lt_of_le_of_lt (zero_le') (Hlv P hP).1)

  have TS : ∀ {l : Γ₀}, lo < l → l < 1 → l ≠ 0 → 1 ≤ levN vc k Z lv d l →
      k + (wle Z lv d l : ℤ) ≤ 0 ∧ 0 ≤ k + (wlt Z lv d l : ℤ) := fun hl1 hl2 hl0 hNl =>
    exps_of_one_le_levN vc k Z lv d lo Hsq Hgen hl1 hl2 hl0 hNl

  have TZ : ∀ P ∈ Z, ¬ (1 ≤ levN vc k Z lv d (lv P)) := by
    intro P hP hNP
    obtain ⟨hle, hge⟩ := TS (Hlv P hP).1 (Hlv P hP).2 (Hlv0 P hP) hNP
    have hsplit := wle_eq_wlt_add_weq Z lv d (lv P)
    have hw := le_weq_of_mem Z lv d hP
    have hdP := hd P hP
    omega

  obtain ⟨hle, hge⟩ := TS h1 h2 h0 hN
  have hsplit := wle_eq_wlt_add_weq Z lv d lam
  have hE : k + (wle Z lv d lam : ℤ) = 0 := by omega
  have hE' : k + (wlt Z lv d lam : ℤ) = 0 := by omega

  obtain ⟨P₁, hP₁⟩ := hZ
  have hne : lv P₁ ≠ lam := by
    intro heq
    exact TZ P₁ hP₁ (heq ▸ hN)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  ·
    set S : Finset Γ₀ := (Z.filter (fun P => lv P < lam)).image lv with hS
    have hSne : S.Nonempty := ⟨lv P₁, Finset.mem_image.mpr ⟨P₁, Finset.mem_filter.mpr ⟨hP₁, hlt⟩, rfl⟩⟩
    obtain ⟨P₂, hP₂, hP₂eq⟩ := Finset.mem_image.mp (Finset.max'_mem S hSne)
    obtain ⟨hP₂Z, hP₂lt⟩ := Finset.mem_filter.mp hP₂
    set α := S.max' hSne with hα
    have hαmax : ∀ P ∈ Z, lv P < lam → lv P ≤ α := fun P hP hl =>
      Finset.le_max' S _ (Finset.mem_image.mpr ⟨P, Finset.mem_filter.mpr ⟨hP, hl⟩, rfl⟩)
    have hα0 : α ≠ 0 := hP₂eq ▸ Hlv0 P₂ hP₂Z
    have hαlam : α < lam := hP₂eq ▸ hP₂lt
    have hgap : ∀ P ∈ Z, lv P ≤ α ∨ lam ≤ lv P := by
      intro P hP
      by_cases hl : lv P < lam
      · exact Or.inl (hαmax P hP hl)
      · exact Or.inr (not_lt.mp hl)
    have hC := levN_eq_mul_zpow vc k Z lv d hα0 (le_of_lt hαlam) hgap
    have hw : wle Z lv d α = wlt Z lv d lam := by
      unfold wle wlt
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext P
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hP, hl⟩; exact ⟨hP, lt_of_le_of_lt hl hαlam⟩
      · rintro ⟨hP, hl⟩; exact ⟨hP, hαmax P hP hl⟩
    rw [hw, hE', zpow_zero, mul_one] at hC

    have : 1 ≤ levN vc k Z lv d (lv P₂) := by rw [hP₂eq, ← hC]; exact hN
    exact TZ P₂ hP₂Z this
  ·
    set S : Finset Γ₀ := (Z.filter (fun P => lam < lv P)).image lv with hS
    have hSne : S.Nonempty := ⟨lv P₁, Finset.mem_image.mpr ⟨P₁, Finset.mem_filter.mpr ⟨hP₁, hgt⟩, rfl⟩⟩
    obtain ⟨P₂, hP₂, hP₂eq⟩ := Finset.mem_image.mp (Finset.min'_mem S hSne)
    obtain ⟨hP₂Z, hP₂gt⟩ := Finset.mem_filter.mp hP₂
    set β := S.min' hSne with hβ
    have hβmin : ∀ P ∈ Z, lam < lv P → β ≤ lv P := fun P hP hl =>
      Finset.min'_le S _ (Finset.mem_image.mpr ⟨P, Finset.mem_filter.mpr ⟨hP, hl⟩, rfl⟩)
    have hlamβ : lam < β := hP₂eq ▸ hP₂gt
    have hgap : ∀ P ∈ Z, lv P ≤ lam ∨ β ≤ lv P := by
      intro P hP
      by_cases hl : lam < lv P
      · exact Or.inr (hβmin P hP hl)
      · exact Or.inl (not_lt.mp hl)
    have hC := levN_eq_mul_zpow vc k Z lv d h0 (le_of_lt hlamβ) hgap
    rw [hE, zpow_zero, mul_one] at hC
    have : 1 ≤ levN vc k Z lv d (lv P₂) := by rw [hP₂eq, hC]; exact hN
    exact TZ P₂ hP₂Z this

end Engine

section PlaceHelpers

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem evalAt_add' (v : Place K F) (hv : v.IsRational) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_add, v.algebraMap_evalAt hv hf, v.algebraMap_evalAt hv hg,
    v.algebraMap_evalAt hv (add_mem hf hg), ← map_add]
  rfl

theorem evalAt_mul' (v : Place K F) (hv : v.IsRational) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f * g) = v.evalAt f * v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_mul, v.algebraMap_evalAt hv hf, v.algebraMap_evalAt hv hg,
    v.algebraMap_evalAt hv (mul_mem hf hg), ← map_mul]
  rfl

theorem evalAt_algebraMap' (v : Place K F) (a : K) : v.evalAt (algebraMap K F a) = a := by
  rw [v.evalAt_of_mem (v.algebraMap_mem' a)]
  have : (⟨algebraMap K F a, v.algebraMap_mem' a⟩ : v.toValuationSubring) =
      algebraMap K v.toValuationSubring a := rfl
  rw [this]
  exact v.residueInv_algebraMap a

theorem evalAt_sub' (v : Place K F) (hv : v.IsRational) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f - g) = v.evalAt f - v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_sub, v.algebraMap_evalAt hv hf, v.algebraMap_evalAt hv hg,
    v.algebraMap_evalAt hv (sub_mem hf hg), ← map_sub]
  rfl

theorem evalAt_pow' (v : Place K F) (hv : v.IsRational) {f : F}
    (hf : f ∈ v.toValuationSubring) (n : ℕ) :
    v.evalAt (f ^ n) = v.evalAt f ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, evalAt_mul' v hv (pow_mem hf n) hf, ih, pow_succ]

theorem evalAt_prod' (v : Place K F) (hv : v.IsRational) {ι : Type*} (s : Finset ι) (f : ι → F)
    (hf : ∀ i ∈ s, f i ∈ v.toValuationSubring) :
    v.evalAt (∏ i ∈ s, f i) = ∏ i ∈ s, v.evalAt (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      evalAt_mul' v hv (hf a (Finset.mem_insert_self a s))
        (prod_mem fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

theorem ord_eq_zero_iff_isUnit (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0) :
    v.ord f = 0 ↔ IsUnit (⟨f, hf⟩ : v.toValuationSubring) := by
  rw [← v.adicValuation_coe_eq_one_iff]
  change -(WithZero.log (v.adicValuation f)) = 0 ↔ v.adicValuation f = 1
  have hne : v.adicValuation f ≠ 0 := v.adicValuation_ne_zero hf0
  constructor
  · intro h
    have h' : WithZero.log (v.adicValuation f) = 0 := neg_eq_zero.mp h
    rw [← WithZero.exp_log hne, h', WithZero.exp_zero]
  · intro h
    rw [h, WithZero.log_one, neg_zero]

theorem adicValuation_le_one_of_mem (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) :
    v.adicValuation f ≤ 1 := by
  have := v.adicValuation_coe ⟨f, hf⟩
  rw [show ((⟨f, hf⟩ : v.toValuationSubring) : F) = f from rfl] at this
  rw [this]
  exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _

theorem ord_pos_of_not_isUnit (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0)
    (hu : ¬ IsUnit (⟨f, hf⟩ : v.toValuationSubring)) : 0 < v.ord f := by
  have hne : v.adicValuation f ≠ 0 := v.adicValuation_ne_zero hf0
  have hle := adicValuation_le_one_of_mem v hf
  have hne1 : v.adicValuation f ≠ 1 := fun h => hu ((v.adicValuation_coe_eq_one_iff ⟨f, hf⟩).mp h)
  have hlt : v.adicValuation f < 1 := lt_of_le_of_ne hle hne1
  change 0 < -(WithZero.log (v.adicValuation f))
  have : WithZero.log (v.adicValuation f) < WithZero.log (1 : ℤᵐ⁰) :=
    (WithZero.log_lt_log hne one_ne_zero).mpr hlt
  rw [WithZero.log_one] at this
  omega

theorem mem_of_ord_eq_zero (v : Place K F) {f : F} (hf0 : f ≠ 0) (h : v.ord f = 0) :
    f ∈ v.toValuationSubring := by
  by_contra hnot
  have hinv : f⁻¹ ∈ v.toValuationSubring := (v.toValuationSubring.mem_or_inv_mem f).resolve_left hnot
  have hinv0 : f⁻¹ ≠ 0 := inv_ne_zero hf0
  have hnu : ¬ IsUnit (⟨f⁻¹, hinv⟩ : v.toValuationSubring) := by
    intro hu
    obtain ⟨u, hu⟩ := hu
    apply hnot
    have hval : ((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring).1 = f := by
      have h1 : ((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring).1 * f⁻¹ = 1 := by
        have := congrArg (fun x : v.toValuationSubring => (x : F)) (u.inv_mul)
        simpa [hu] using this
      have h2 := congrArg (· * f) h1
      simpa [mul_assoc, inv_mul_cancel₀ hf0] using h2
    rw [← hval]
    exact SetLike.coe_mem _
  have hpos := ord_pos_of_not_isUnit v hinv hinv0 hnu
  rw [v.ord_inv, h] at hpos
  exact absurd hpos (lt_irrefl _)

theorem mem_of_ord_nonneg (v : Place K F) {f : F} (hf0 : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  by_contra hnot
  have hinv : f⁻¹ ∈ v.toValuationSubring := (v.toValuationSubring.mem_or_inv_mem f).resolve_left hnot
  have hinv0 : f⁻¹ ≠ 0 := inv_ne_zero hf0
  have hnu : ¬ IsUnit (⟨f⁻¹, hinv⟩ : v.toValuationSubring) := by
    intro hu
    obtain ⟨u, hu⟩ := hu
    apply hnot
    have hval : ((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring).1 = f := by
      have h1 : ((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring).1 * f⁻¹ = 1 := by
        have := congrArg (fun x : v.toValuationSubring => (x : F)) (u.inv_mul)
        simpa [hu] using this
      have h2 := congrArg (· * f) h1
      simpa [mul_assoc, inv_mul_cancel₀ hf0] using h2
    rw [← hval]
    exact SetLike.coe_mem _
  have hpos := ord_pos_of_not_isUnit v hinv hinv0 hnu
  rw [v.ord_inv] at hpos
  omega

theorem ord_nonneg_of_mem (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0) :
    0 ≤ v.ord f := by
  by_cases hu : IsUnit (⟨f, hf⟩ : v.toValuationSubring)
  · rw [(ord_eq_zero_iff_isUnit v hf hf0).mpr hu]
  · exact le_of_lt (ord_pos_of_not_isUnit v hf hf0 hu)

theorem evalAt_eq_zero_iff_not_isUnit (v : Place K F) (hv : v.IsRational) {f : F}
    (hf : f ∈ v.toValuationSubring) :
    v.evalAt f = 0 ↔ ¬ IsUnit (⟨f, hf⟩ : v.toValuationSubring) := by
  rw [← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff,
    ← v.algebraMap_evalAt hv hf, map_eq_zero_iff _ v.algebraMap_residueField_injective]

theorem evalAt_eq_zero_iff_ord_pos (v : Place K F) (hv : v.IsRational) {f : F}
    (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0) :
    v.evalAt f = 0 ↔ 0 < v.ord f := by
  rw [evalAt_eq_zero_iff_not_isUnit v hv hf, ← ord_eq_zero_iff_isUnit v hf hf0]
  have := ord_nonneg_of_mem v hf hf0
  omega

theorem ord_algebraMap' (v : Place K F) (c : K) : v.ord (algebraMap K F c) = 0 := by
  by_cases hc : c = 0
  · rw [hc, map_zero, Place.ord_zero]
  · let uu : v.toValuationSubringˣ :=
      ⟨⟨algebraMap K F c, v.algebraMap_mem' c⟩, ⟨algebraMap K F c⁻¹, v.algebraMap_mem' c⁻¹⟩,
        Subtype.ext (by simp [hc]), Subtype.ext (by simp [hc])⟩
    exact v.ord_coe_unit uu

theorem ord_add_eq_of_lt' (v : Place K F) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0)
    (h : v.ord f < v.ord g) : v.ord (f + g) = v.ord f := by
  have hfne : v.adicValuation f ≠ 0 := v.adicValuation_ne_zero hf
  have hgne : v.adicValuation g ≠ 0 := v.adicValuation_ne_zero hg
  have hlt : v.adicValuation g < v.adicValuation f := by
    rw [← WithZero.log_lt_log hgne hfne]
    change -(WithZero.log (v.adicValuation f)) < -(WithZero.log (v.adicValuation g)) at h
    omega
  have := Valuation.map_add_eq_of_lt_left v.adicValuation hlt
  change -(WithZero.log (v.adicValuation (f + g))) = -(WithZero.log (v.adicValuation f))
  rw [this]

end PlaceHelpers

section AnnulusCalculus

open scoped Classical

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]

theorem eq_of_evalAt_param_eq (An : Annulus A F) {P Q : Place L F} (hP : P ∈ An.dom)
    (hQ : Q ∈ An.dom) (h : P.evalAt An.param = Q.evalAt An.param) : P = Q := by
  obtain ⟨-, -, ⟨hA, hm⟩, hne, hmod⟩ := An.mem_dom P hP
  obtain ⟨R, -, huniq⟩ := An.existsUnique_evalAt_eq ⟨_, hA⟩ hm hne hmod
  exact (huniq P ⟨hP, rfl⟩).trans (huniq Q ⟨hQ, h.symm⟩).symm

theorem param_sub_ne_zero (An : Annulus A F) {P : Place L F} (hP : P ∈ An.dom) :
    An.param - algebraMap L F (P.evalAt An.param) ≠ 0 := by
  intro h0
  have h1 := An.ord_param_sub P hP
  rw [h0, Place.ord_zero] at h1
  exact zero_ne_one h1

theorem ord_param_sub_algebraMap (An : Annulus A F) {Q : Place L F} (hQ : Q ∈ An.dom) (a : L) :
    Q.ord (An.param - algebraMap L F a) = if Q.evalAt An.param = a then 1 else 0 := by
  split_ifs with h
  · rw [← h]; exact An.ord_param_sub Q hQ
  · have h1 : Q.ord (An.param - algebraMap L F (Q.evalAt An.param)) = 1 := An.ord_param_sub Q hQ
    have hc : algebraMap L F (Q.evalAt An.param - a) ≠ 0 := by
      rw [map_ne_zero_iff _ (algebraMap L F).injective]
      exact sub_ne_zero.mpr h
    have hg : An.param - algebraMap L F (Q.evalAt An.param) ≠ 0 := param_sub_ne_zero An hQ
    have hlt : Q.ord (algebraMap L F (Q.evalAt An.param - a)) <
        Q.ord (An.param - algebraMap L F (Q.evalAt An.param)) := by
      rw [ord_algebraMap', h1]; exact zero_lt_one
    have key := ord_add_eq_of_lt' Q hc hg hlt
    rw [ord_algebraMap'] at key
    have hrw : An.param - algebraMap L F a =
        algebraMap L F (Q.evalAt An.param - a) + (An.param - algebraMap L F (Q.evalAt An.param)) := by
      rw [map_sub]; ring
    rw [hrw, key]

theorem ord_param_sub_evalAt (An : Annulus A F) {P Q : Place L F} (hP : P ∈ An.dom)
    (hQ : Q ∈ An.dom) :
    Q.ord (An.param - algebraMap L F (P.evalAt An.param)) = if Q = P then 1 else 0 := by
  rw [ord_param_sub_algebraMap An hQ]
  by_cases h : Q = P
  · subst h; simp
  · rw [if_neg h, if_neg]
    exact fun h' => h (eq_of_evalAt_param_eq An hQ hP h')

theorem ord_finset_prod {ι : Type*} (Q : Place L F) (s : Finset ι) (g : ι → F)
    (hg : ∀ i ∈ s, g i ≠ 0) : Q.ord (∏ i ∈ s, g i) = ∑ i ∈ s, Q.ord (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hga : g a ≠ 0 := hg a (Finset.mem_insert_self a s)
    have hgs : ∀ i ∈ s, g i ≠ 0 := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    rw [Q.ord_mul hga (Finset.prod_ne_zero_iff.mpr hgs), ih hgs]

theorem dom_facts (An : Annulus A F) {P : Place L F} (hP : P ∈ An.dom) :
    P.IsRational ∧ An.param ∈ P.toValuationSubring ∧ P.evalAt An.param ∈ A ∧
      A.valuation (P.evalAt An.param) < 1 ∧ P.evalAt An.param ≠ 0 ∧
      A.valuation (An.modulus : L) < A.valuation (P.evalAt An.param) := by
  obtain ⟨hrat, hz, ⟨hA, hm⟩, hne, m, hm𝔪, hmod⟩ := An.mem_dom P hP
  refine ⟨hrat, hz, hA, (A.valuation_lt_one_iff ⟨_, hA⟩).mp hm, hne, ?_⟩
  have hvm : A.valuation (m : L) < 1 := (A.valuation_lt_one_iff m).mp hm𝔪
  have hpos : 0 < A.valuation (P.evalAt An.param) :=
    lt_of_le_of_ne (zero_le') (Ne.symm ((Valuation.ne_zero_iff _).mpr hne))
  rw [hmod, map_mul]
  calc A.valuation (P.evalAt An.param) * A.valuation (m : L)
      < A.valuation (P.evalAt An.param) * 1 := mul_lt_mul_of_pos_left hvm hpos
    _ = A.valuation (P.evalAt An.param) := mul_one _

theorem ord_param_eq_zero (An : Annulus A F) {P : Place L F} (hP : P ∈ An.dom) : P.ord An.param = 0 := by
  obtain ⟨hrat, hz, -, -, hne, -⟩ := dom_facts An hP
  have hz0 : An.param ≠ 0 := by
    intro h; apply hne; rw [h]
    have := evalAt_algebraMap' P (0 : L)
    rwa [map_zero] at this
  have hnn := ord_nonneg_of_mem P hz hz0
  have hnot : ¬ (0 < P.ord An.param) := fun hpos => hne ((evalAt_eq_zero_iff_ord_pos P hrat hz hz0).mpr hpos)
  omega

theorem exists_mem_dom_valuation_eq (An : Annulus A F) {σ : A.ValueGroup}
    (h1 : A.valuation (An.modulus : L) < σ) (h2 : σ < 1) :
    ∃ Q ∈ An.dom, A.valuation (Q.evalAt An.param) = σ := by
  obtain ⟨x, hx⟩ := A.valuation_surjective σ
  have hσ0 : σ ≠ 0 := ne_of_gt (lt_of_le_of_lt (zero_le') h1)
  have hx0 : x ≠ 0 := by
    intro h; apply hσ0; rw [← hx, h, map_zero]
  have hxA : x ∈ A := A.mem_of_valuation_le_one x (by rw [hx]; exact le_of_lt h2)
  have hxm : (⟨x, hxA⟩ : A) ∈ maximalIdeal A := (A.valuation_lt_one_iff ⟨x, hxA⟩).mpr (by rw [hx]; exact h2)

  set mm : L := (An.modulus : L) * x⁻¹ with hmm
  have hvmm : A.valuation mm < 1 := by
    rw [hmm, map_mul, map_inv₀, hx]
    calc A.valuation (An.modulus : L) * σ⁻¹ < σ * σ⁻¹ := by
          rw [mul_comm _ σ⁻¹, mul_comm σ σ⁻¹]
          exact mul_lt_mul_of_pos_left h1 (inv_pos.mpr (lt_of_le_of_ne (zero_le') (Ne.symm hσ0)))
      _ = 1 := mul_inv_cancel₀ hσ0
  have hmmA : mm ∈ A := A.mem_of_valuation_le_one mm (le_of_lt hvmm)
  have hmmm : (⟨mm, hmmA⟩ : A) ∈ maximalIdeal A := (A.valuation_lt_one_iff ⟨mm, hmmA⟩).mpr hvmm
  have hmod : (An.modulus : L) = x * mm := by
    rw [hmm, mul_comm x, mul_assoc, inv_mul_cancel₀ hx0, mul_one]
  obtain ⟨Q, ⟨hQ, hQx⟩, -⟩ := An.existsUnique_evalAt_eq ⟨x, hxA⟩ hxm hx0 ⟨⟨mm, hmmA⟩, hmmm, hmod⟩
  exact ⟨Q, hQ, by rw [hQx, hx]⟩

end AnnulusCalculus

section Core

open scoped Classical

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]

theorem exists_sq_valueGroup [IsAlgClosed L] (x : A.ValueGroup) : ∃ s, s * s = x := by
  obtain ⟨a, rfl⟩ := A.valuation_surjective x
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_eq_mul_self a
  exact ⟨A.valuation t, by rw [← map_mul, ← ht]⟩

theorem valuation_sub_lt_one_core [IsAlgClosed L] [HasPrincipalDivisors L F] (An : Annulus A F)
    (g : F) (hg0 : g ≠ 0) (hg : ∀ P ∈ An.dom, P.ord g = 0)
    (hu : ∀ P ∈ An.dom, A.valuation (P.evalAt g) = 1)
    {P Q : Place L F} (hP : P ∈ An.dom) (hQ : Q ∈ An.dom) :
    A.valuation (P.evalAt g - Q.evalAt g) < 1 := by

  set v := A.valuation with hv
  set z := An.param with hz
  set b : L := Q.evalAt g with hb
  set G : F := g - algebraMap L F b with hG
  have hgmem : ∀ R ∈ An.dom, g ∈ R.toValuationSubring := fun R hR => mem_of_ord_eq_zero R hg0 (hg R hR)
  have hGmem : ∀ R ∈ An.dom, G ∈ R.toValuationSubring := fun R hR =>
    sub_mem (hgmem R hR) (R.algebraMap_mem' b)
  have hGeval : ∀ R ∈ An.dom, R.evalAt G = R.evalAt g - b := by
    intro R hR
    rw [hG, evalAt_sub' R (dom_facts An hR).1 (hgmem R hR) (R.algebraMap_mem' b), evalAt_algebraMap']

  by_cases hG0 : G = 0
  · have : P.evalAt g = b := by
      have h := hGeval P hP
      rw [hG0] at h
      have h0 : P.evalAt (0 : F) = 0 := by
        have := evalAt_algebraMap' P (0 : L); rwa [map_zero] at this
      rw [h0] at h
      exact (sub_eq_zero.mp h.symm)
    rw [this, hb, sub_self, map_zero]
    exact zero_lt_one

  have hGle : ∀ R ∈ An.dom, v (R.evalAt G) ≤ 1 := by
    intro R hR
    rw [hGeval R hR]
    refine le_trans (Valuation.map_sub v _ _) (max_le (le_of_eq (hu R hR)) (le_of_eq ?_))
    exact hu Q hQ

  obtain ⟨DG, hDG, -⟩ := HasPrincipalDivisors.exists_divisor (K := L) G hG0
  set Z : Finset (Place L F) := DG.support.filter (· ∈ An.dom) with hZ
  have hZdom : ∀ R ∈ Z, R ∈ An.dom := fun R hR => (Finset.mem_filter.mp hR).2
  have hZpos : ∀ R ∈ Z, 0 < DG R := by
    intro R hR
    obtain ⟨hsupp, hdom⟩ := Finset.mem_filter.mp hR
    have hne : DG R ≠ 0 := Finsupp.mem_support_iff.mp hsupp
    have hnn : 0 ≤ DG R := by rw [hDG R]; exact ord_nonneg_of_mem R (hGmem R hdom) hG0
    omega
  set d : Place L F → ℕ := fun R => (DG R).toNat with hd
  have hdcast : ∀ R ∈ Z, (d R : ℤ) = DG R := fun R hR => Int.toNat_of_nonneg (le_of_lt (hZpos R hR))
  have hdpos : ∀ R ∈ Z, 0 < d R := by
    intro R hR
    have := hdcast R hR
    have := hZpos R hR
    omega
  have hDG_of_not_mem : ∀ R ∈ An.dom, R ∉ Z → DG R = 0 := by
    intro R hR hRZ
    by_contra hne
    exact hRZ (Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hne, hR⟩)

  have hQZ : Q ∈ Z := by
    have h0 : Q.evalAt G = 0 := by rw [hGeval Q hQ, hb, sub_self]
    have hpos : 0 < Q.ord G := (evalAt_eq_zero_iff_ord_pos Q (dom_facts An hQ).1 (hGmem Q hQ) hG0).mp h0
    refine Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr ?_, hQ⟩
    rw [hDG Q]; exact ne_of_gt hpos

  set zp : F := ∏ R ∈ Z, (z - algebraMap L F (R.evalAt z)) ^ d R with hzp
  have hzp0 : zp ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun R hR => pow_ne_zero _ (param_sub_ne_zero An (hZdom R hR))
  have hzp_ord : ∀ R ∈ An.dom, R.ord zp = DG R := by
    intro R hR
    rw [hzp, ord_finset_prod R Z _ (fun R' hR' => pow_ne_zero _ (param_sub_ne_zero An (hZdom R' hR')))]
    have : ∀ R' ∈ Z, R.ord ((z - algebraMap L F (R'.evalAt z)) ^ d R') = if R = R' then (d R' : ℤ) else 0 := by
      intro R' hR'
      rw [← zpow_natCast, R.ord_zpow, ord_param_sub_evalAt An (hZdom R' hR') hR]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq]
    split_ifs with hmem
    · exact hdcast R hmem
    · exact (hDG_of_not_mem R hR hmem).symm
  have hzp_mem : ∀ R ∈ An.dom, zp ∈ R.toValuationSubring := fun R hR =>
    prod_mem fun R' _ => pow_mem (sub_mem (dom_facts An hR).2.1 (R.algebraMap_mem' _)) _
  have hzp_eval : ∀ R ∈ An.dom, R.evalAt zp = ∏ R' ∈ Z, (R.evalAt z - R'.evalAt z) ^ d R' := by
    intro R hR
    have hrat := (dom_facts An hR).1
    have hzR := (dom_facts An hR).2.1
    rw [hzp, evalAt_prod' R hrat Z _ (fun R' _ => pow_mem (sub_mem hzR (R.algebraMap_mem' _)) _)]
    refine Finset.prod_congr rfl fun R' _ => ?_
    rw [evalAt_pow' R hrat (sub_mem hzR (R.algebraMap_mem' _)), evalAt_sub' R hrat hzR (R.algebraMap_mem' _),
      evalAt_algebraMap']

  set H : F := G * zp⁻¹ with hH
  have hH0 : H ≠ 0 := mul_ne_zero hG0 (inv_ne_zero hzp0)
  have hHord : ∀ R ∈ An.dom, R.ord H = 0 := by
    intro R hR
    rw [hH, R.ord_mul hG0 (inv_ne_zero hzp0), R.ord_inv, hzp_ord R hR, ← hDG R]
    ring
  have hHmem : ∀ R ∈ An.dom, H ∈ R.toValuationSubring := fun R hR => mem_of_ord_eq_zero R hH0 (hHord R hR)
  have hGH : G = H * zp := by rw [hH, inv_mul_cancel_right₀ hzp0]
  obtain ⟨k', c', hc'0, hunit⟩ := An.unit_principle H hH0 hHord
  have hvc' : v c' ≠ 0 := (Valuation.ne_zero_iff v).mpr hc'0
  have hHval : ∀ R ∈ An.dom, v (R.evalAt H) = v c' * (v (R.evalAt z)) ^ k' := by
    intro R hR
    obtain ⟨hmem, hun⟩ := hunit R hR
    have h1 : v (R.evalAt H * c'⁻¹ * R.evalAt z ^ (-k')) = 1 := (A.valuation_eq_one_iff ⟨_, hmem⟩).mp hun
    have hzR0 : v (R.evalAt z) ≠ 0 := (Valuation.ne_zero_iff v).mpr (dom_facts An hR).2.2.2.2.1
    rw [map_mul, map_mul, map_inv₀, map_zpow₀, zpow_neg] at h1
    calc v (R.evalAt H) = v (R.evalAt H) * (v c')⁻¹ * (v (R.evalAt z) ^ k')⁻¹ * (v c' * v (R.evalAt z) ^ k') := by
          rw [mul_assoc (v (R.evalAt H) * (v c')⁻¹), mul_comm (v c'), ← mul_assoc ((v (R.evalAt z) ^ k')⁻¹),
            inv_mul_cancel₀ (zpow_ne_zero k' hzR0), one_mul, mul_assoc, inv_mul_cancel₀ hvc', mul_one]
      _ = v c' * v (R.evalAt z) ^ k' := by rw [h1, one_mul]

  have hGval : ∀ R ∈ An.dom, R ∉ Z →
      v (R.evalAt G) = v c' * (v (R.evalAt z)) ^ k' * ∏ R' ∈ Z, v (R.evalAt z - R'.evalAt z) ^ d R' := by
    intro R hR hRZ
    rw [hGH, evalAt_mul' R (dom_facts An hR).1 (hHmem R hR) (hzp_mem R hR), map_mul, hHval R hR,
      hzp_eval R hR, map_prod]
    congr 1
    exact Finset.prod_congr rfl fun R' _ => map_pow _ _ _

  set lv : Place L F → A.ValueGroup := fun R => v (R.evalAt z) with hlv
  set lo : A.ValueGroup := v (An.modulus : L) with hlo
  have Hlv : ∀ R ∈ Z, lo < lv R ∧ lv R < 1 := fun R hR =>
    ⟨(dom_facts An (hZdom R hR)).2.2.2.2.2, (dom_facts An (hZdom R hR)).2.2.2.1⟩

  have hA : ∀ R ∈ An.dom, v (R.evalAt G) ≤ levN (v c') k' Z lv d (lv R) := by
    intro R hR
    by_cases hRZ : R ∈ Z
    · have hpos : 0 < R.ord G := by rw [← hDG R]; exact hZpos R hRZ
      have h0 : R.evalAt G = 0 := (evalAt_eq_zero_iff_ord_pos R (dom_facts An hR).1 (hGmem R hR) hG0).mpr hpos
      rw [h0, map_zero]; exact zero_le'
    · rw [hGval R hR hRZ]
      unfold levN
      refine mul_le_mul_right ?_ _
      refine Finset.prod_le_prod' fun R' _ => pow_le_pow_left' ?_ _
      calc v (R.evalAt z - R'.evalAt z) ≤ max (v (R.evalAt z)) (v (R'.evalAt z)) := Valuation.map_sub v _ _
        _ = max (lv R) (lv R') := rfl

  have hgen : ∀ σ, lo < σ → σ < 1 → σ ≠ 0 → (∀ R' ∈ Z, lv R' ≠ σ) → levN (v c') k' Z lv d σ ≤ 1 := by
    intro σ h1 h2 _ hσZ
    obtain ⟨R, hR, hRσ⟩ := exists_mem_dom_valuation_eq An h1 h2
    have hRZ : R ∉ Z := fun h => hσZ R h hRσ
    have heq : levN (v c') k' Z lv d σ = v (R.evalAt G) := by
      rw [hGval R hR hRZ]
      unfold levN
      rw [← hRσ]
      congr 1
      refine Finset.prod_congr rfl fun R' hR' => ?_
      congr 1
      have hne : v (R.evalAt z) ≠ v (R'.evalAt z) := by rw [hRσ]; exact Ne.symm (hσZ R' hR')
      rw [sub_eq_add_neg, Valuation.map_add_of_distinct_val v (by rwa [Valuation.map_neg]), Valuation.map_neg]
    rw [heq]
    exact hGle R hR

  have hlt : v (P.evalAt G) < 1 := by
    by_contra hnot
    have h1 : 1 ≤ levN (v c') k' Z lv d (lv P) := le_trans (not_lt.mp hnot) (hA P hP)
    exact false_of_one_le_levN (v c') k' Z lv d lo hdpos ⟨Q, hQZ⟩ Hlv exists_sq_valueGroup hgen
      (dom_facts An hP).2.2.2.2.2 (dom_facts An hP).2.2.2.1
      ((Valuation.ne_zero_iff v).mpr (dom_facts An hP).2.2.2.2.1) h1
  rw [hGeval P hP] at hlt
  exact hlt

end Core

section General

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]

theorem evalAt_inv' (v : Place L F) (hv : v.IsRational) {f : F} (hf0 : f ≠ 0) (hf : v.ord f = 0) :
    v.evalAt f⁻¹ = (v.evalAt f)⁻¹ := by
  have hmem : f ∈ v.toValuationSubring := mem_of_ord_eq_zero v hf0 hf
  have hmem' : f⁻¹ ∈ v.toValuationSubring :=
    mem_of_ord_eq_zero v (inv_ne_zero hf0) (by rw [v.ord_inv, hf, neg_zero])
  have hne : v.evalAt f ≠ 0 := fun h0 => by
    have := (evalAt_eq_zero_iff_ord_pos v hv hmem hf0).mp h0
    omega
  have h1 : v.evalAt f * v.evalAt f⁻¹ = 1 := by
    rw [← evalAt_mul' v hv hmem hmem', mul_inv_cancel₀ hf0]
    have := evalAt_algebraMap' v (1 : L)
    rwa [map_one] at this
  exact (eq_inv_of_mul_eq_one_right h1)

theorem evalAt_zpow' (v : Place L F) (hv : v.IsRational) {f : F} (hf0 : f ≠ 0) (hf : v.ord f = 0) (n : ℤ) :
    v.evalAt (f ^ n) = v.evalAt f ^ n := by
  have hmem : f ∈ v.toValuationSubring := mem_of_ord_eq_zero v hf0 hf
  cases n with
  | ofNat k => rw [Int.ofNat_eq_natCast, zpow_natCast, zpow_natCast, evalAt_pow' v hv hmem]
  | negSucc k =>
    rw [zpow_negSucc, zpow_negSucc]
    have hk : v.ord (f ^ (k + 1)) = 0 := by rw [← zpow_natCast, v.ord_zpow, hf, mul_zero]
    rw [evalAt_inv' v hv (pow_ne_zero _ hf0) hk, evalAt_pow' v hv hmem]

theorem valuation_sub_lt_one [IsAlgClosed L] [HasPrincipalDivisors L F] (An : Annulus A F)
    (f : F) (hf0 : f ≠ 0) (hf : ∀ P ∈ An.dom, P.ord f = 0) (m : ℤ) (c : L) (hc : c ≠ 0)
    (hu : ∀ P ∈ An.dom, ∃ h : P.evalAt f * c⁻¹ * (P.evalAt An.param) ^ (-m) ∈ A, IsUnit (⟨_, h⟩ : A))
    {P Q : Place L F} (hP : P ∈ An.dom) (hQ : Q ∈ An.dom) :
    A.valuation (P.evalAt f * c⁻¹ * (P.evalAt An.param) ^ (-m) -
      Q.evalAt f * c⁻¹ * (Q.evalAt An.param) ^ (-m)) < 1 := by
  set z := An.param with hz
  have hz0 : z ≠ 0 := by
    intro h
    have := (dom_facts An hP).2.2.2.2.1
    apply this
    rw [← hz, h]
    have h0 := evalAt_algebraMap' P (0 : L)
    rwa [map_zero] at h0
  set g : F := f * algebraMap L F c⁻¹ * z ^ (-m) with hg
  have hcF : algebraMap L F c⁻¹ ≠ 0 := (map_ne_zero _).mpr (inv_ne_zero hc)
  have hzm0 : z ^ (-m) ≠ 0 := zpow_ne_zero _ hz0
  have hg0 : g ≠ 0 := mul_ne_zero (mul_ne_zero hf0 hcF) hzm0
  have hzord : ∀ R ∈ An.dom, R.ord (z ^ (-m)) = 0 := fun R hR => by
    rw [R.ord_zpow, ord_param_eq_zero An hR, mul_zero]
  have hgord : ∀ R ∈ An.dom, R.ord g = 0 := by
    intro R hR
    rw [hg, R.ord_mul (mul_ne_zero hf0 hcF) hzm0, R.ord_mul hf0 hcF, hf R hR, ord_algebraMap', hzord R hR]
    ring
  have hgeval : ∀ R ∈ An.dom, R.evalAt g = R.evalAt f * c⁻¹ * (R.evalAt z) ^ (-m) := by
    intro R hR
    have hrat := (dom_facts An hR).1
    have hfm : f ∈ R.toValuationSubring := mem_of_ord_eq_zero R hf0 (hf R hR)
    have hcm : algebraMap L F c⁻¹ ∈ R.toValuationSubring := R.algebraMap_mem' _
    have hzm : z ^ (-m) ∈ R.toValuationSubring := mem_of_ord_eq_zero R hzm0 (hzord R hR)
    rw [hg, evalAt_mul' R hrat (mul_mem hfm hcm) hzm, evalAt_mul' R hrat hfm hcm, evalAt_algebraMap',
      evalAt_zpow' R hrat hz0 (ord_param_eq_zero An hR)]
  have hgu : ∀ R ∈ An.dom, A.valuation (R.evalAt g) = 1 := by
    intro R hR
    obtain ⟨hmem, hun⟩ := hu R hR
    rw [hgeval R hR]
    exact (A.valuation_eq_one_iff ⟨_, hmem⟩).mp hun
  have := valuation_sub_lt_one_core An g hg0 hgord hgu hP hQ
  rwa [hgeval P hP, hgeval Q hQ] at this

end General

end AF8ConstRed

theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F] [HasPrincipalDivisors L F]
    (An : Annulus A F) (f : F) (hf0 : f ≠ 0) (hf : ∀ P ∈ An.dom, P.ord f = 0)
    (m : ℤ) (c : L) (hc : c ≠ 0)
    (hu : ∀ P ∈ An.dom, ∃ h : P.evalAt f * c⁻¹ * (P.evalAt An.param) ^ (-m) ∈ A, IsUnit (⟨_, h⟩ : A))
    (P Q : Place L F) (hP : P ∈ An.dom) (hQ : Q ∈ An.dom) :
    A.valuation (P.evalAt f * c⁻¹ * (P.evalAt An.param) ^ (-m) -
      Q.evalAt f * c⁻¹ * (Q.evalAt An.param) ^ (-m)) < 1 :=
  AF8ConstRed.valuation_sub_lt_one An f hf0 hf m c hc hu hP hQ

end S_AlgebraicCurve_Annulus_valuation_sub_lt_one_of_forall_isUnit
end P2MW
export P2MW.S_AlgebraicCurve_Annulus_valuation_sub_lt_one_of_forall_isUnit (solution)
