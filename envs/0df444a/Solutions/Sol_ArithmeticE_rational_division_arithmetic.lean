-- Prove2me | solution 1 for ArithmeticE.rational_division_arithmetic
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T15:58:57.855701+00:00
-- url     : https://prove2.me/submissions/fd9f2ac3-ef3d-4511-a4d2-7702929f2f25

import Definitions.Def_rationalEArithmetic
open scoped BigOperators
open ArithmeticE Filter
namespace EulerEDivision

lemma normalized_division_integral (a : ℕ → ℚ) (D n : ℕ)
    (h : ∀ k ≤ n, ∃ z : ℤ, (D:ℚ)*a k=z) :
    ∃ z : ℤ, (D:ℚ)*((n.factorial:ℚ)*∑ k ∈ Finset.range (n+1), a k/(k.factorial:ℚ))=z := by
  have hterms : ∀ k ∈ Finset.range (n+1), ∃ z : ℤ,
      (D:ℚ)*((n.factorial:ℚ)*(a k/(k.factorial:ℚ)))=z := by
    intro k hk
    have hkn : k ≤ n := by simpa using Finset.mem_range.mp hk
    obtain ⟨z,hz⟩ := h k hkn
    obtain ⟨d,hd⟩ := Nat.factorial_dvd_factorial hkn
    refine ⟨d*z, ?_⟩
    rw [hd]
    push_cast
    have hf : (k.factorial:ℚ) ≠ 0 := by positivity
    field_simp
    linear_combination (d:ℚ)*hz
  choose z hz using hterms
  refine ⟨∑ k ∈ Finset.range (n+1), if hk : k ∈ Finset.range (n+1) then z k hk else 0, ?_⟩
  simp only [Finset.mul_sum,Int.cast_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simpa [hk] using hz k hk

lemma tail_bound (a : ℕ → ℚ) (C : ℝ) (hC : 1 ≤ C)
    (ha : ∀ n : ℕ, |(a n:ℝ)| ≤ C^(n+1)) (n k : ℕ) :
    |(n.factorial:ℝ)*((a (k+n+1):ℝ)/((k+n+1).factorial:ℝ))| ≤
      C^(n+2)*(C^k/(k.factorial:ℝ)) := by
  have hfac : (n.factorial:ℝ)*(k.factorial:ℝ) ≤ ((k+n+1).factorial:ℝ) := by
    exact_mod_cast (Nat.le_of_dvd (Nat.factorial_pos (n+k))
      (Nat.factorial_mul_factorial_dvd_factorial_add n k)).trans
        (Nat.factorial_le (by omega : n+k ≤ k+n+1))
  rw [abs_mul,abs_of_nonneg (by positivity : (0:ℝ) ≤ n.factorial),abs_div,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (k+n+1).factorial)]
  calc (n.factorial:ℝ)*(|(a (k+n+1):ℝ)|/((k+n+1).factorial:ℝ))
      ≤ (n.factorial:ℝ)*(C^(k+n+1+1)/((k+n+1).factorial:ℝ)) := by gcongr; exact ha _
    _ ≤ (n.factorial:ℝ)*(C^(k+n+1+1)/((n.factorial:ℝ)*(k.factorial:ℝ))) := by
      gcongr
    _ = C^(n+2)*(C^k/(k.factorial:ℝ)) := by
      rw [show k+n+1+1=n+2+k by omega,pow_add]
      field_simp

lemma normalized_division_bound (a : ℕ → ℚ) (C : ℝ) (hC : 1 ≤ C)
    (ha : ∀ n : ℕ, |(a n:ℝ)| ≤ C^(n+1))
    (hz : HasSum (fun n : ℕ => (a n:ℝ)/(n.factorial:ℝ)) 0) (n : ℕ) :
    |(n.factorial:ℝ)*∑ k ∈ Finset.range (n+1), (a k:ℝ)/(k.factorial:ℝ)| ≤
      C^(n+2)*(∑' k : ℕ, C^k/(k.factorial:ℝ)) := by
  have htail := (hasSum_nat_add_iff' (n+1)).mpr hz
  have hm := htail.mul_left (n.factorial:ℝ)
  have hg := (Real.summable_pow_div_factorial C).hasSum.mul_left (C^(n+2))
  have hbound := hm.norm_le_of_bounded hg (fun k => by
    simpa only [Real.norm_eq_abs,Nat.add_assoc] using tail_bound a C hC ha n k)
  simpa [Real.norm_eq_abs,sub_zero,zero_sub,mul_neg,abs_neg] using hbound
lemma arithmetic_division (a : ℕ → ℚ) (ha : RationalArithmetic a)
    (hz : HasSum (fun n : ℕ => (a n:ℝ)/(n.factorial:ℝ)) 0) :
    RationalArithmetic (fun n => (n.factorial:ℚ)*∑ k ∈ Finset.range (n+1), a k/(k.factorial:ℚ)) := by
  obtain ⟨C,hC,hbound,hden⟩ := ha
  let S := ∑' k : ℕ, C^k/(k.factorial:ℝ)
  have hS : 0 ≤ S := tsum_nonneg (fun k => by positivity)
  let K := max C (C^2*(S+1))
  have hCK : C ≤ K := le_max_left ..
  have hK : 1 ≤ K := hC.trans hCK
  refine ⟨K,hK,?_,?_⟩
  · intro n
    push_cast
    calc |(n.factorial:ℝ)*∑ k ∈ Finset.range (n+1), (a k:ℝ)/(k.factorial:ℝ)|
        ≤ C^(n+2)*S := normalized_division_bound a C hC hbound hz n
      _ = C^n*(C^2*S) := by rw [pow_add]; ring
      _ ≤ K^n*K := by
        apply mul_le_mul
        · exact pow_le_pow_left₀ (by linarith) hCK n
        · exact (mul_le_mul_of_nonneg_left (by linarith : S ≤ S+1) (sq_nonneg C)).trans (le_max_right ..)
        · positivity
        · positivity
      _ = K^(n+1) := (pow_succ K n).symm
  · intro n
    obtain ⟨D,hD,hDC,hDi⟩ := hden n
    refine ⟨D,hD,hDC.trans (pow_le_pow_left₀ (by linarith) hCK _),?_⟩
    intro k hk
    exact normalized_division_integral a D k (fun j hj => hDi j (hj.trans hk))
end EulerEDivision


theorem solution (a : ℕ → ℚ) (ha : RationalArithmetic a)
    (hz : HasSum (fun n : ℕ => (a n:ℝ)/(n.factorial:ℝ)) 0) :
    RationalArithmetic (fun n => (n.factorial:ℚ)*∑ k ∈ Finset.range (n+1), a k/(k.factorial:ℚ)) := by
  exact EulerEDivision.arithmetic_division a ha hz

#print axioms solution
