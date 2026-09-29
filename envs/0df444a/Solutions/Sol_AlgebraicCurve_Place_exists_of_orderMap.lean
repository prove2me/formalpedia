-- Prove2me | solution 1 for AlgebraicCurve.Place.exists_of_orderMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/d8751259-a283-5de7-9c81-09ff41d24034

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_exists_of_orderMap

set_option autoImplicit false

open WithZero

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F]
    (μ : F → WithTop ℤ) (h_top : ∀ x, μ x = ⊤ ↔ x = 0)
    (h_mul : ∀ x y, μ (x * y) = μ x + μ y) (h_add : ∀ x y, min (μ x) (μ y) ≤ μ (x + y))
    (h_const : ∀ c : K, c ≠ 0 → μ (algebraMap K F c) = 0) (h_nontriv : ∃ x, 0 < μ x ∧ μ x ≠ ⊤) :
    ∃ (P : AlgebraicCurve.Place K F) (e : ℕ), 0 < e ∧
      (∀ x, x ∈ P.toValuationSubring ↔ 0 ≤ μ x) ∧
      ∀ x, x ≠ 0 → μ x = (((e : ℤ) * P.ord x : ℤ) : WithTop ℤ) := by
  classical

  let w : WithTop ℤ → ℤᵐ⁰ := fun a => WithTop.recTopCoe (0 : ℤᵐ⁰) (fun n : ℤ => exp (-n)) a
  have w_top : w ⊤ = 0 := rfl
  have w_coe : ∀ n : ℤ, w n = exp (-n) := fun n => rfl
  have w_zero : w 0 = 1 := by rw [← WithTop.coe_zero, w_coe, neg_zero, exp_zero]
  have w_add : ∀ a b, w (a + b) = w a * w b := by
    intro a b
    induction a with
    | top => rw [top_add, w_top, zero_mul]
    | coe a =>
      induction b with
      | top => rw [add_top, w_top, mul_zero]
      | coe b => rw [← WithTop.coe_add, w_coe, w_coe, w_coe, ← exp_add, neg_add]
  have w_le : ∀ a b, w a ≤ w b ↔ b ≤ a := by
    intro a b
    induction a with
    | top =>
      induction b with
      | top => simp [w_top]
      | coe b => simp [w_top, w_coe]
    | coe a =>
      induction b with
      | top => simp [w_top, w_coe]
      | coe b =>
        rw [w_coe, w_coe, exp_le_exp, neg_le_neg_iff, WithTop.coe_le_coe]
  have μ_one : μ 1 = 0 := by simpa using h_const 1 one_ne_zero
  let v : Valuation F ℤᵐ⁰ :=
    { toFun := fun x => w (μ x)
      map_zero' := by show w (μ 0) = 0; rw [(h_top 0).mpr rfl, w_top]
      map_one' := by show w (μ 1) = 1; rw [μ_one, w_zero]
      map_mul' := fun x y => by show w (μ (x * y)) = w (μ x) * w (μ y); rw [h_mul, w_add]
      map_add_le_max' := fun x y => by
        show w (μ (x + y)) ≤ max (w (μ x)) (w (μ y))
        rcases le_total (μ x) (μ y) with hxy | hxy
        · refine le_trans ?_ (le_max_left _ _)
          rw [w_le]; exact le_trans (by simp [hxy]) (h_add x y)
        · refine le_trans ?_ (le_max_right _ _)
          rw [w_le]; exact le_trans (by simp [hxy]) (h_add x y) }
  have v_apply : ∀ x, v x = w (μ x) := fun x => rfl
  have mem_iff : ∀ x, x ∈ v.valuationSubring ↔ 0 ≤ μ x := by
    intro x
    rw [Valuation.mem_valuationSubring_iff, v_apply, ← w_zero, w_le]

  obtain ⟨x₀, hx₀pos, hx₀top⟩ := h_nontriv
  have hx₀ne : x₀ ≠ 0 := fun h => hx₀top ((h_top x₀).mpr h)
  haveI hnt : v.IsNontrivial := by
    refine ⟨x₀, ?_, ?_⟩
    · rw [v_apply]
      obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hx₀top
      rw [← hn, w_coe]; exact exp_ne_zero
    · rw [v_apply, ne_eq, ← w_zero]
      intro h
      have h1 := (w_le 0 (μ x₀)).mp h.ge
      exact absurd (lt_of_lt_of_le hx₀pos h1) (lt_irrefl _)
  haveI : Nontrivial (MonoidWithZeroHom.valueGroup (.ofClass v)) := inferInstance
  haveI : IsCyclic (MonoidWithZeroHom.valueGroup (.ofClass v)) := inferInstance
  haveI hPIR : IsPrincipalIdealRing v.valuationSubring :=
    Valuation.valuationSubring_isPrincipalIdealRing v

  have hK : ∀ a : K, algebraMap K F a ∈ v.valuationSubring := by
    intro a
    rw [mem_iff]
    rcases eq_or_ne a 0 with rfl | ha
    · rw [map_zero, (h_top 0).mpr rfl]; exact le_top
    · rw [h_const a ha]
  have hne : v.valuationSubring ≠ ⊤ := by
    intro h
    have : x₀⁻¹ ∈ v.valuationSubring := h ▸ ValuationSubring.mem_top _
    rw [mem_iff] at this
    have hinv : μ x₀⁻¹ + μ x₀ = 0 := by rw [← h_mul, inv_mul_cancel₀ hx₀ne, μ_one]
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hx₀top
    have hitop : μ x₀⁻¹ ≠ ⊤ := by
      rw [ne_eq, h_top]; exact inv_ne_zero hx₀ne
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hitop
    rw [← hn, ← hm, ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_eq_coe] at hinv
    rw [← hm, ← WithTop.coe_zero, WithTop.coe_le_coe] at this
    rw [← hn, ← WithTop.coe_zero, WithTop.coe_lt_coe] at hx₀pos
    omega
  let P : AlgebraicCurve.Place K F :=
    { toValuationSubring := v.valuationSubring
      algebraMap_mem' := hK
      ne_top' := hne
      isPrincipalIdealRing' := hPIR }

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible P.toValuationSubring
  have hϖ0 : (ϖ : F) ≠ 0 := by
    simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hϖ.ne_zero
  have hϖtop : μ (ϖ : F) ≠ ⊤ := by rwa [ne_eq, h_top]
  have hϖmem : 0 ≤ μ (ϖ : F) := (mem_iff _).mp ϖ.2

  have μ_unit : ∀ u : (P.toValuationSubring)ˣ, μ ((u : P.toValuationSubring) : F) = 0 := by
    intro u
    have h1 : 0 ≤ μ ((u : P.toValuationSubring) : F) :=
      (mem_iff _).mp (u : P.toValuationSubring).2
    have h2 : 0 ≤ μ (((u⁻¹ : (P.toValuationSubring)ˣ) : P.toValuationSubring) : F) :=
      (mem_iff _).mp ((u⁻¹ : (P.toValuationSubring)ˣ) : P.toValuationSubring).2
    have h3 : μ ((u : P.toValuationSubring) : F) +
        μ (((u⁻¹ : (P.toValuationSubring)ˣ) : P.toValuationSubring) : F) = 0 := by
      rw [← h_mul, ← Subring.coe_mul, Units.mul_inv, OneMemClass.coe_one, μ_one]
    have hut : μ ((u : P.toValuationSubring) : F) ≠ ⊤ := by
      intro h; rw [h, top_add] at h3; exact WithTop.top_ne_zero h3
    have hu't : μ (((u⁻¹ : (P.toValuationSubring)ˣ) : P.toValuationSubring) : F) ≠ ⊤ := by
      intro h; rw [h, add_top] at h3; exact WithTop.top_ne_zero h3
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp hut
    obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.mp hu't
    rw [← ha, ← hb, ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_eq_coe] at h3
    rw [← ha, ← WithTop.coe_zero, WithTop.coe_le_coe] at h1
    rw [← hb, ← WithTop.coe_zero, WithTop.coe_le_coe] at h2
    rw [← ha, ← WithTop.coe_zero, WithTop.coe_eq_coe]
    omega

  have hϖpos : 0 < μ (ϖ : F) := by
    rcases hϖmem.lt_or_eq with h | h
    · exact h
    · exfalso
      apply hϖ.not_isUnit
      have hinv : (ϖ : F)⁻¹ ∈ P.toValuationSubring := by
        refine (mem_iff _).mpr ?_
        have : μ (ϖ : F)⁻¹ + μ (ϖ : F) = 0 := by rw [← h_mul, inv_mul_cancel₀ hϖ0, μ_one]
        rw [← h, add_zero] at this
        rw [this]
      exact ⟨⟨ϖ, ⟨(ϖ : F)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hϖ0),
        Subtype.ext (inv_mul_cancel₀ hϖ0)⟩, rfl⟩
  obtain ⟨e, he⟩ := WithTop.ne_top_iff_exists.mp hϖtop
  rw [← he, ← WithTop.coe_zero, WithTop.coe_lt_coe] at hϖpos
  refine ⟨P, e.toNat, by omega, mem_iff, fun x hx => ?_⟩

  obtain ⟨u, hu⟩ := P.exists_unit_mul_zpow hx hϖ
  have μ_zpow : ∀ n : ℤ, μ ((ϖ : F) ^ n) = ((n * e : ℤ) : WithTop ℤ) := by
    have μ_pow : ∀ n : ℕ, μ ((ϖ : F) ^ n) = ((n * e : ℤ) : WithTop ℤ) := by
      intro n
      induction n with
      | zero => rw [pow_zero, μ_one]; simp
      | succ n ih =>
        rw [pow_succ, h_mul, ih, ← he, ← WithTop.coe_add]
        congr 1; push_cast; ring
    intro n
    rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
    · rw [zpow_natCast, μ_pow]
    · rw [zpow_neg, zpow_natCast]
      have hpm : μ ((ϖ : F) ^ m)⁻¹ + μ ((ϖ : F) ^ m) = 0 := by
        rw [← h_mul, inv_mul_cancel₀ (pow_ne_zero _ hϖ0), μ_one]
      have hpt : μ ((ϖ : F) ^ m)⁻¹ ≠ ⊤ := by
        rw [ne_eq, h_top]; exact inv_ne_zero (pow_ne_zero _ hϖ0)
      obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.mp hpt
      rw [μ_pow, ← hc, ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_eq_coe] at hpm
      rw [← hc, WithTop.coe_eq_coe]
      linarith
  have hfin : μ x = ((P.ord x * e : ℤ) : WithTop ℤ) := by
    conv_lhs => rw [hu]
    rw [h_mul, μ_unit, zero_add, μ_zpow]
  rw [hfin, Int.toNat_of_nonneg hϖpos.le, mul_comm]

end S_AlgebraicCurve_Place_exists_of_orderMap
end P2MW
export P2MW.S_AlgebraicCurve_Place_exists_of_orderMap (solution)
