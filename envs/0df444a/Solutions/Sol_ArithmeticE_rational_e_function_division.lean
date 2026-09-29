-- Prove2me | solution 1 for ArithmeticE.rational_e_function_division
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T16:10:13.159924+00:00
-- url     : https://prove2.me/submissions/408805d4-cdf6-41f5-918d-881734447fe9

import Theorems.Thm_ArithmeticE_rational_series_division
import Theorems.Thm_ArithmeticE_differential_operator_division_identity
open PowerSeries
namespace EulerEHolonomic
lemma polynomial_annihilator_division (g : PowerSeries ℂ) (p : ℕ → Polynomial ℚ) (m : ℕ)
    (hp : p m ≠ 0)
    (h : ∑ k ∈ Finset.range (m+1), ((p k).map (algebraMap ℚ ℂ):PowerSeries ℂ)*
      (PowerSeries.derivative ℂ)^[k] ((1-PowerSeries.X)*g)=0) :
    ∃ q : ℕ → Polynomial ℚ, q m ≠ 0 ∧
      ∑ k ∈ Finset.range (m+1), ((q k).map (algebraMap ℚ ℂ):PowerSeries ℂ)*
        (PowerSeries.derivative ℂ)^[k] g=0 := by
  let q : ℕ → Polynomial ℚ := fun k => (1-Polynomial.X)*p k-
    if k < m then ((k+1:ℕ):Polynomial ℚ)*p (k+1) else 0
  refine ⟨q,?_,?_⟩
  · simp only [q,lt_self_iff_false,if_false,sub_zero]
    apply mul_ne_zero _ hp
    intro hzero
    have := congrArg (Polynomial.coeff · 1) hzero
    norm_num [Polynomial.coeff_one] at this
  · have hh := ArithmeticE.differential_operator_division_identity
      (fun k => ((p k).map (algebraMap ℚ ℂ):PowerSeries ℂ)) g m
    rw [h] at hh
    rw [hh]
    simp only [q,Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_one,Polynomial.map_X,
      Polynomial.coe_sub,Polynomial.coe_mul,Polynomial.coe_one,Polynomial.coe_X,
      sub_mul,Finset.sum_sub_distrib]
    congr 1
    · simp [← Finset.mul_sum,mul_assoc]
    · rw [Finset.sum_range_succ]
      simp only [lt_self_iff_false,if_false,Polynomial.map_zero,Polynomial.coe_zero,zero_mul,add_zero]
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k < m := Finset.mem_range.mp hk
      simp only [if_pos hk',Polynomial.map_mul,Polynomial.map_natCast,Polynomial.coe_mul]
      congr 2
      exact map_natCast (Polynomial.coeToPowerSeries.ringHom : Polynomial ℂ →+* PowerSeries ℂ) (k+1)
end EulerEHolonomic
open ArithmeticE PowerSeries
namespace EulerEHolonomic
lemma rational_e_function_division (a : ℕ → ℚ) (ha : RationalArithmetic a)
    (hz : HasSum (fun n : ℕ => (a n:ℝ)/(n.factorial:ℝ)) 0)
    (p : ℕ → Polynomial ℚ) (m : ℕ) (hp : p m ≠ 0)
    (hode : ∑ k ∈ Finset.range (m+1), ((p k).map (algebraMap ℚ ℂ):PowerSeries ℂ)*
      (PowerSeries.derivative ℂ)^[k] (PowerSeries.mk (fun n => (a n:ℂ)/(n.factorial:ℂ)))=0) :
    ∃ g : PowerSeries ℂ, RationalSeriesArithmetic g ∧
      (1-PowerSeries.X)*g=PowerSeries.mk (fun n => (a n:ℂ)/(n.factorial:ℂ)) ∧
      ∃ q : ℕ → Polynomial ℚ, q m ≠ 0 ∧
        ∑ k ∈ Finset.range (m+1), ((q k).map (algebraMap ℚ ℂ):PowerSeries ℂ)*
          (PowerSeries.derivative ℂ)^[k] g=0 := by
  obtain ⟨g,hg,he⟩ := ArithmeticE.rational_series_division a ha hz
  refine ⟨g,hg,he,?_⟩
  apply polynomial_annihilator_division g p m hp
  simpa only [he] using hode
end EulerEHolonomic

theorem solution (a : ℕ → ℚ) (ha : RationalArithmetic a)
    (hz : HasSum (fun n : ℕ => (a n:ℝ)/(n.factorial:ℝ)) 0)
    (p : ℕ → Polynomial ℚ) (m : ℕ) (hp : p m ≠ 0)
    (hode : ∑ k ∈ Finset.range (m+1), ((p k).map (algebraMap ℚ ℂ):PowerSeries ℂ)*
      (PowerSeries.derivative ℂ)^[k] (PowerSeries.mk (fun n => (a n:ℂ)/(n.factorial:ℂ)))=0) :
    ∃ g : PowerSeries ℂ, RationalSeriesArithmetic g ∧
      (1-PowerSeries.X)*g=PowerSeries.mk (fun n => (a n:ℂ)/(n.factorial:ℂ)) ∧
      ∃ q : ℕ → Polynomial ℚ, q m ≠ 0 ∧
        ∑ k ∈ Finset.range (m+1), ((q k).map (algebraMap ℚ ℂ):PowerSeries ℂ)*
          (PowerSeries.derivative ℂ)^[k] g=0 := by
  exact EulerEHolonomic.rational_e_function_division a ha hz p m hp hode

#print axioms solution
