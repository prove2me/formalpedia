-- Prove2me | Definitions.Def_Yukon_56f5e02e27ca1815c809ecfe
-- name    : Yukon_56f5e02e27ca1815c809ecfe
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T05:45:03.310225+00:00
-- url     : https://prove2.me/theorems/e53c74ef-85ba-4fb1-8916-a17dad3a03f1
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.BoundaryTailValuation.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.BoundaryTailValuation.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/BoundaryTailValuation.lean
--
--   yukon-proof-operation:foundation-direct-938b4ebd017951cdf6191625501232d46ae965a635fdf87e30f9aa40fe9a486f
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiYzAxNmE0Yzk3MTMxMjZiM2I1YjhmNTg2YTRjMDgwMzA3Mjk0ZTQ5ZmI3YmE1NjJmNTg3M2E1NThmOTg0ZDAwMiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTkzOGI0ZWJkMDE3OTUxY2RmNjE5MTYyNTUwMTIzMmQ0NmFlOTY1YTYzNWZkZjg3ZTMwZjlhYTQwZmU5YTQ4NmYiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl81NmY1ZTAyZTI3Y2ExODE1YzgwOWVjZmUiLCJ2IjoyfQ]

import Definitions.Def_Yukon_3e4b96ce1a94735c97e0e660

import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical






































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.BoundaryTail

open scoped BigOperators

noncomputable section

variable {L : Type*} [Field L]

-- Resolve equality case splits directly in the larger serialized import environment.
local instance  _root_.ProximityPrize.SubmissionLower.BoundaryTail.instDecidableEq_proximityPrize : DecidableEq L := Classical.decEq L

def refinedMonomial (n j : ℕ) (H G J C : L) : L :=
  H ^ j * G ^ (n - 1 - j) * J ^ (n - 2 - 2 * j) * C

def refinedWeight (n j : ℕ) (a b c : ℤ) : ℤ :=
  (j : ℤ) * a + ((n - 1 - j : ℕ) : ℤ) * b +
    ((n - 2 - 2 * j : ℕ) : ℤ) * c

theorem refinedWeight_eq {n j : ℕ} (hn : 2 ≤ n) (hj : j < n)
    (a b c : ℤ) :
    refinedWeight n j a b c =
      (j : ℤ) * a + ((n : ℤ) - 1 - j) * b +
        max ((n : ℤ) - 2 - 2 * j) 0 * c := by
  have hsub : ((n - 1 - j : ℕ) : ℤ) = (n : ℤ) - 1 - j := by omega
  have htail : ((n - 2 - 2 * j : ℕ) : ℤ) =
      max ((n : ℤ) - 2 - 2 * j) 0 := by omega
  simp only [refinedWeight, hsub, htail]

theorem refined_monomial_value_le_exp
    (v : Valuation L (WithZero (Multiplicative ℤ)))
    {n j : ℕ} (hn : 2 ≤ n) (hj : j < n)
    (H G J C : L) (h g q A B D : ℤ)
    (hH : v H ≤ WithZero.exp h) (hG : v G ≤ WithZero.exp g)
    (hJ : v J ≤ WithZero.exp q)
    (hC : v C ≤ WithZero.exp
      ((j : ℤ) * (B - A) + ((min (2 * j) (n - 2) : ℕ) : ℤ) * D)) :
    v (refinedMonomial n j H G J C) ≤ WithZero.exp
      (((n - 1 : ℕ) : ℤ) * B + ((n - 2 : ℕ) : ℤ) * D -
        refinedWeight n j (A - h) (B - g) (D - q)) := by
  have hpow (x : L) (e : ℤ) (hx : v x ≤ WithZero.exp e) (k : ℕ) :
      v x ^ k ≤ WithZero.exp ((k : ℤ) * e) := by
    rw [← nsmul_eq_mul, WithZero.exp_nsmul]
    exact pow_le_pow_left₀ zero_le hx k
  have hsub : ((n - 1 - j : ℕ) : ℤ) + j = ((n - 1 : ℕ) : ℤ) := by omega
  have hmin : ((n - 2 - 2 * j : ℕ) : ℤ) +
      ((min (2 * j) (n - 2) : ℕ) : ℤ) = ((n - 2 : ℕ) : ℤ) := by omega
  unfold refinedMonomial
  simp only [map_mul, map_pow]
  calc
    _ ≤ WithZero.exp ((j : ℤ) * h) *
        WithZero.exp (((n - 1 - j : ℕ) : ℤ) * g) *
        WithZero.exp (((n - 2 - 2 * j : ℕ) : ℤ) * q) *
        WithZero.exp ((j : ℤ) * (B - A) +
          ((min (2 * j) (n - 2) : ℕ) : ℤ) * D) :=
      mul_le_mul' (mul_le_mul' (mul_le_mul' (hpow H h hH j)
        (hpow G g hG (n - 1 - j))) (hpow J q hJ (n - 2 - 2 * j))) hC
    _ = _ := by
      rw [← WithZero.exp_add, ← WithZero.exp_add, ← WithZero.exp_add]
      congr 1
      unfold refinedWeight
      nlinarith [congrArg (fun t : ℤ => t * B) hsub,
        congrArg (fun t : ℤ => t * D) hmin]

theorem refined_monomial_value_le
    (v : Valuation L (WithZero (Multiplicative ℤ)))
    {n j : ℕ} (hn : 2 ≤ n) (hj : j < n)
    (H G J C : L) (hH : H ≠ 0) (hG : G ≠ 0) (hJ : J ≠ 0)
    (A B D : ℤ)
    (hC : v C ≤ WithZero.exp
      ((j : ℤ) * (B - A) + ((min (2 * j) (n - 2) : ℕ) : ℤ) * D)) :
    v (refinedMonomial n j H G J C) ≤ WithZero.exp
      (((n - 1 : ℕ) : ℤ) * B + ((n - 2 : ℕ) : ℤ) * D -
        refinedWeight n j (A - (v H).log) (B - (v G).log) (D - (v J).log)) :=
  refined_monomial_value_le_exp v hn hj H G J C _ _ _ A B D
    (WithZero.le_exp_of_log_le (le_refl _))
    (WithZero.le_exp_of_log_le (le_refl _))
    (WithZero.le_exp_of_log_le (le_refl _)) hC

theorem zero_sum_has_no_strictly_dominant_term
    (v : Valuation L (WithZero (Multiplicative ℤ)))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (T : ι → L) (i : ι)
    (hi : T i ≠ 0) (hsum : ∑ j, T j = 0) :
    ¬ (∀ j, j ≠ i → v (T j) < v (T i)) := by
  intro hlt
  have hsmall : v (∑ j ∈ Finset.univ.erase i, T j) < v (T i) := by
    apply v.map_sum_lt (by simpa using hi)
    intro j hj
    exact hlt j (Finset.mem_erase.mp hj).1
  have hsplit : (∑ j ∈ Finset.univ.erase i, T j) + T i = 0 := by
    rw [Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    exact hsum
  have hneg : (∑ j ∈ Finset.univ.erase i, T j) = -T i :=
    eq_neg_of_add_eq_zero_left hsplit
  rw [hneg, v.map_neg] at hsmall
  exact lt_irrefl _ hsmall

theorem first_tail_shifted_constraint
    (v : Valuation L (WithZero (Multiplicative ℤ)))
    {n : ℕ} (hn : 2 ≤ n) (H G J : L)
    (hH : H ≠ 0) (hG : G ≠ 0) (hJ : J ≠ 0)
    (C : Fin n → L) (A B D : ℤ)
    (hD : (v J).log ≤ D)
    (hC : ∀ j, v (C j) ≤ WithZero.exp
      ((j.val : ℤ) * (B - A) + ((min (2 * j.val) (n - 2) : ℕ) : ℤ) * D))
    (hlead : v (C ⟨0, by omega⟩) = 1)
    (hzero : ∑ j, refinedMonomial n j.val H G J (C j) = 0) :
    (A - (v H).log) - (B - (v G).log) ≤ 2 * (D - (v J).log) := by
  classical
  by_contra hgap
  let i : Fin n := ⟨0, by omega⟩
  let T : Fin n → L := fun j => refinedMonomial n j.val H G J (C j)
  let P : ℤ := ((n - 1 : ℕ) : ℤ) * B + ((n - 2 : ℕ) : ℤ) * D
  let a := A - (v H).log
  let b := B - (v G).log
  let c := D - (v J).log
  have hleadval : v (T i) = WithZero.exp
      (P - (((n - 1 : ℕ) : ℤ) * b + ((n - 2 : ℕ) : ℤ) * c)) := by
    have hGv : v G ≠ 0 := (Valuation.ne_zero_iff v).mpr hG
    have hJv : v J ≠ 0 := (Valuation.ne_zero_iff v).mpr hJ
    simp only [T, i, refinedMonomial, pow_zero, one_mul, Nat.sub_zero,
      Nat.mul_zero, map_mul, map_pow, hlead, mul_one]
    rw [← WithZero.exp_log (pow_ne_zero (n - 1) hGv),
      ← WithZero.exp_log (pow_ne_zero (n - 2) hJv), ← WithZero.exp_add]
    congr 1
    simp only [WithZero.log_pow, nsmul_eq_mul, P, b, c]
    ring
  have hi : T i ≠ 0 := by
    intro hz
    have := hleadval
    rw [hz, map_zero] at this
    exact WithZero.exp_ne_zero this.symm
  apply zero_sum_has_no_strictly_dominant_term v T i hi hzero
  intro j hji
  have hjpos : 1 ≤ (j.val : ℤ) := by
    have : j.val ≠ 0 := by
      intro hz
      apply hji
      exact Fin.ext hz
    omega
  have hsep := leading_separation
    (n := (n : ℤ)) (j := (j.val : ℤ)) (a := a) (b := b) (c := c)
    (by omega) hjpos (by omega) (by dsimp [c]; omega) (by exact lt_of_not_ge hgap)
  have hvalue := refined_monomial_value_le v hn j.isLt H G J (C j)
    hH hG hJ A B D (hC j)
  change v (T j) ≤ WithZero.exp (P - refinedWeight n j.val a b c) at hvalue
  apply lt_of_le_of_lt hvalue
  rw [hleadval]
  apply WithZero.exp_lt_exp.mpr
  rw [refinedWeight_eq hn j.isLt]
  have hsub1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
  have hsub2 : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := by omega
  rw [hsub1, hsub2]
  linarith

theorem later_tail_value_le_exp
    (v : Valuation L (WithZero (Multiplicative ℤ)))
    {n : ℕ} (hn : 2 ≤ n) (H G J : L)
    (C : Fin n → L) (h g q A B D : ℤ)
    (hH : v H ≤ WithZero.exp h) (hG : v G ≤ WithZero.exp g)
    (hJ : v J ≤ WithZero.exp q)
    (hA : h ≤ A) (hB : g ≤ B) (hD : q ≤ D)
    (hgap : (A - h) - (B - g) ≤ 2 * (D - q))
    (hC : ∀ j, v (C j) ≤ WithZero.exp
      ((j.val : ℤ) * (B - A) + ((min (2 * j.val) (n - 2) : ℕ) : ℤ) * D)) :
    v (∑ j, refinedMonomial n j.val H G J (C j)) ≤ WithZero.exp
      ((2 * (((n - 1 : ℕ) : ℤ) * B + ((n - 2 : ℕ) : ℤ) * D) -
          2 * ((n - 1 : ℕ) : ℤ) * (A - h) +
          (n : ℤ) * max ((A - h) - (B - g)) 0) / 2) := by
  apply v.map_sum_le
  intro j _
  apply le_trans (refined_monomial_value_le_exp v hn j.isLt H G J (C j)
    h g q A B D hH hG hJ (hC j))
  apply WithZero.exp_le_exp.mpr
  apply (Int.le_ediv_iff_mul_le (by decide : (0 : ℤ) < 2)).mpr
  have hweight := weighted_tail_bound
    (n := (n : ℤ)) (j := (j.val : ℤ))
    (a := A - h) (b := B - g) (c := D - q)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hgap
  rw [refinedWeight_eq hn j.isLt]
  have hsub : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
  rw [hsub]
  nlinarith

theorem exists_admissible_exponents
    (v : Valuation L (WithZero (Multiplicative ℤ)))
    (H G J : L) (A B D : ℤ) (hH : H ≠ 0) (hAB : A ≤ B)
    (hA : (v H).log ≤ A)
    (hB : G ≠ 0 → (v G).log ≤ B) (hD : J ≠ 0 → (v J).log ≤ D)
    (hfirst : G ≠ 0 → J ≠ 0 →
      (A - (v H).log) - (B - (v G).log) ≤ 2 * (D - (v J).log)) :
    ∃ g q : ℤ,
      v G ≤ WithZero.exp g ∧ v J ≤ WithZero.exp q ∧
      g ≤ B ∧ q ≤ D ∧
      (A - (v H).log) - (B - g) ≤ 2 * (D - q) ∧
      max ((A - (v H).log) - (B - g)) 0 =
        max (max (v (G / H)).log 0 - (B - A)) 0 := by
  have hHv : v H ≠ 0 := (Valuation.ne_zero_iff v).mpr hH
  have hJchoice (g : ℤ)
      (hg : J ≠ 0 → (A - (v H).log) - (B - g) ≤ 2 * (D - (v J).log)) :
      ∃ q : ℤ, v J ≤ WithZero.exp q ∧ q ≤ D ∧
        (A - (v H).log) - (B - g) ≤ 2 * (D - q) := by
    by_cases hz : J = 0
    · refine ⟨D - max ((A - (v H).log) - (B - g)) 0, ?_, ?_, ?_⟩
      · simp only [hz, map_zero]; exact zero_le
      · omega
      · omega
    · exact ⟨(v J).log, WithZero.le_exp_of_log_le (le_refl _), hD hz, hg hz⟩
  by_cases hG : G = 0
  · obtain ⟨q, hqv, hqD, hq⟩ := hJchoice ((v H).log + B - A) (by
      intro hJ
      have := hD hJ
      omega)
    refine ⟨(v H).log + B - A, q, ?_, hqv, ?_, hqD, hq, ?_⟩
    · simp only [hG, map_zero]; exact zero_le
    · omega
    · simp only [hG, zero_div, map_zero, WithZero.log_zero]
      omega
  · obtain ⟨q, hqv, hqD, hq⟩ := hJchoice (v G).log (hfirst hG)
    refine ⟨(v G).log, q, WithZero.le_exp_of_log_le (le_refl _),
      hqv, hB hG, hqD, hq, ?_⟩
    have hGv : v G ≠ 0 := (Valuation.ne_zero_iff v).mpr hG
    rw [map_div₀, WithZero.log_div hGv hHv]
    omega

theorem normalized_tail_pole_le
    (v : Valuation L (WithZero (Multiplicative ℤ)))
    {n : ℕ} (hn : 2 ≤ n) (H G J : L) (hH : H ≠ 0)
    (C : Fin n → L) (A u t : ℤ) (ht : 0 ≤ t) (htu : t ≤ u) (huA : u ≤ A)
    (hA : (v H).log ≤ A)
    (hB : G ≠ 0 → (v G).log ≤ A + 2 * u - t)
    (hD : J ≠ 0 → (v J).log ≤ A - u)
    (hfirst : G ≠ 0 → J ≠ 0 →
      (A - (v H).log) - (A + 2 * u - t - (v G).log) ≤
        2 * (A - u - (v J).log))
    (hC : ∀ j, v (C j) ≤ WithZero.exp
      ((j.val : ℤ) * (2 * u - t) +
        ((min (2 * j.val) (n - 2) : ℕ) : ℤ) * (A - u))) :
    2 * max (v (H ^ 3 * (∑ j, refinedMonomial n j.val H G J (C j)) /
      H ^ (n - 1))).log 0 ≤
      2 * (((n : ℤ) + 1) * A - ((n : ℤ) - 1) * t) +
        (n : ℤ) * max (2 * u) (t + max (v (G / H)).log 0) := by
  let T := ∑ j, refinedMonomial n j.val H G J (C j)
  let theta := max (2 * u) (t + max (v (G / H)).log 0)
  have htheta0 : 0 ≤ theta := by dsimp [theta]; omega
  have hnormal0 : 0 ≤ ((n : ℤ) + 1) * A - ((n : ℤ) - 1) * t := by
    have hprod := mul_nonneg (show 0 ≤ (n : ℤ) - 1 by omega)
      (show 0 ≤ A - t by omega)
    nlinarith
  have hright0 : 0 ≤ 2 * (((n : ℤ) + 1) * A - ((n : ℤ) - 1) * t) +
      (n : ℤ) * theta := by positivity
  change 2 * max (v (H ^ 3 * T / H ^ (n - 1))).log 0 ≤ _
  by_cases hT : T = 0
  · simpa only [hT, mul_zero, zero_div, map_zero, WithZero.log_zero,
      max_self, mul_zero] using hright0
  obtain ⟨g, q, hg, hq, hgB, hqD, hgap, hr⟩ := exists_admissible_exponents
    v H G J A (A + 2 * u - t) (A - u) hH (by omega) hA hB hD hfirst
  have hc' : ∀ j, v (C j) ≤ WithZero.exp
      ((j.val : ℤ) * ((A + 2 * u - t) - A) +
        ((min (2 * j.val) (n - 2) : ℕ) : ℤ) * (A - u)) := by
    convert hC using 1 <;> ring
  have hvalue := later_tail_value_le_exp v hn H G J C (v H).log g q
    A (A + 2 * u - t) (A - u)
    (WithZero.le_exp_of_log_le (le_refl _)) hg hq hA hgB hqD hgap hc'
  let Q : ℤ := 2 * (((n - 1 : ℕ) : ℤ) * (A + 2 * u - t) +
      ((n - 2 : ℕ) : ℤ) * (A - u)) -
      2 * ((n - 1 : ℕ) : ℤ) * (A - (v H).log) +
      (n : ℤ) * max ((A - (v H).log) - (A + 2 * u - t - g)) 0
  change v T ≤ WithZero.exp (Q / 2) at hvalue
  have hTv : v T ≠ 0 := (Valuation.ne_zero_iff v).mpr hT
  have hlog : (v T).log ≤ Q / 2 := by
    simpa only [WithZero.log_exp] using
      (WithZero.log_le_log hTv WithZero.exp_ne_zero).mpr hvalue
  have htwolog : 2 * (v T).log ≤ Q := by omega
  have htheta := max_shift_identity (u := u) (v := t) (p := (v (G / H)).log) ht htu
  have htheta_ge : 0 ≤ theta - 2 * u := by dsimp [theta]; omega
  change max (theta - 2 * u) 0 = _ at htheta
  rw [max_eq_left htheta_ge] at htheta
  have hdelta : max ((A - (v H).log) - (A + 2 * u - t - g)) 0 = theta - 2 * u := by
    rw [hr, htheta]
    omega
  have hHv : v H ≠ 0 := (Valuation.ne_zero_iff v).mpr hH
  have hlogcut : (v (H ^ 3 * T / H ^ (n - 1))).log =
      (4 - (n : ℤ)) * (v H).log + (v T).log := by
    rw [map_div₀, map_mul, map_pow, map_pow,
      WithZero.log_div (mul_ne_zero (pow_ne_zero 3 hHv) hTv) (pow_ne_zero _ hHv),
      WithZero.log_mul (pow_ne_zero 3 hHv) hTv]
    simp only [WithZero.log_pow, nsmul_eq_mul, Nat.cast_ofNat]
    have hsub : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
    rw [hsub]
    ring
  rw [hlogcut]
  by_cases hnonneg : 0 ≤ (4 - (n : ℤ)) * (v H).log + (v T).log
  · rw [max_eq_left hnonneg]
    dsimp [Q] at htwolog
    rw [hdelta] at htwolog
    have hsub1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
    have hsub2 : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := by omega
    rw [hsub1, hsub2] at htwolog
    nlinarith
  · rw [max_eq_right (by omega), mul_zero]
    exact hright0

end

end ProximityPrize.SubmissionLower.BoundaryTail


