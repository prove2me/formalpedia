-- Prove2me | Definitions.Def_row23_rh_supp_RHLegendreCellBounds
-- name    : row23_rh_supp_RHLegendreCellBounds
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:18:01.508785+00:00
-- url     : https://prove2.me/theorems/ba48b3f5-fd17-4eb5-a90d-94669ee143c6
-- title:
--   Row 23 RH support: RHLegendreCellBounds
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendreBernstein
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace DusartLegendreSmoothing
open Polynomial Finset MeasureTheory intervalIntegral
 theorem cell_integral_abs_bound (p : ℝ[X]) (n : ℕ) (a b : ℝ)
    (hab : a ≤ b) (c : Fin (n+1) → ℝ)
    (he : ∀ t ∈ Set.Icc (0:ℝ) 1,
      p.eval (a+(b-a)*t)=∑ i : Fin (n+1), c i*(bernsteinPolynomial ℝ n i.val).eval t) :
    (∫ t : ℝ in a..b, |p.eval t|) ≤ (b-a)*(∑ i : Fin (n+1), |c i|)/((n:ℝ)+1) := by
  have hs : (∫ t : ℝ in 0..1, |p.eval (a+(b-a)*t)|)=
      ∫ t : ℝ in 0..1, |∑ i : Fin (n+1), c i*(bernsteinPolynomial ℝ n i.val).eval t| := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact congrArg abs (he t (by simpa using ht))
  have ha : (b-a)*(∫ t : ℝ in 0..1, |p.eval (a+(b-a)*t)|)=
      ∫ t : ℝ in a..b, |p.eval t| := by
    have he : a+(b-a)=b := by ring
    simpa only [smul_eq_mul,mul_zero,add_zero,mul_one,he] using
      intervalIntegral.smul_integral_comp_add_mul (a:=0) (b:=1) (fun t : ℝ => |p.eval t|) (b-a) a
  rw [←ha,hs]
  have hh := mul_le_mul_of_nonneg_left (bernstein_integral_abs_bound n c) (sub_nonneg.mpr hab)
  simpa only [mul_div_assoc] using hh
 theorem partition_integral_abs_bound (p : ℝ[X]) (k : ℕ) (nodes : ℕ → ℝ)
    (hn0 : nodes 0=0) (hn1 : nodes k=1) (bounds : ℕ → ℝ)
    (hc : ∀ i < k, (∫ t : ℝ in nodes i..nodes (i+1), |p.eval t|) ≤ bounds i) :
    (∫ t : ℝ in 0..1, |p.eval t|) ≤ ∑ i ∈ Finset.range k, bounds i := by
  have hi : ∀ i < k, IntervalIntegrable (fun t : ℝ => |p.eval t|) volume (nodes i) (nodes (i+1)) := by
    intro i hi
    exact p.continuous.abs.intervalIntegrable _ _
  have he := intervalIntegral.sum_integral_adjacent_intervals hi
  rw [hn0,hn1] at he
  rw [←he]
  exact Finset.sum_le_sum (fun i hi => hc i (Finset.mem_range.mp hi))
 theorem rational_cell_integral_abs_bound (p : ℚ[X]) (n : ℕ) (a b : ℚ)
    (hab : a ≤ b) (S : ℤ) (hS : 0 < S) (cs : Fin (n+1) → ℤ)
    (hp : p.comp (C a+C (b-a)*X)=
      ∑ i : Fin (n+1), C ((cs i:ℚ)/(S:ℚ))*bernsteinPolynomial ℚ n i.val) :
    (∫ t : ℝ in (a:ℝ)..(b:ℝ), |(p.map (Rat.castHom ℝ)).eval t|) ≤
      ((b-a:ℚ):ℝ)*(∑ i : Fin (n+1), |(cs i:ℝ)|)/((S:ℝ)*((n:ℝ)+1)) := by
  have he (t : ℝ) :
      (p.map (Rat.castHom ℝ)).eval ((a:ℝ)+((b:ℝ)-(a:ℝ))*t)=
      ∑ i : Fin (n+1), ((cs i:ℝ)/(S:ℝ))*(bernsteinPolynomial ℝ n i.val).eval t := by
    have hh := congrArg (fun q : ℚ[X] => (q.map (Rat.castHom ℝ)).eval t) hp
    simpa only [Polynomial.map_comp,Polynomial.map_add,Polynomial.map_C,Polynomial.map_mul,
      Polynomial.map_X,Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_C,
      Polynomial.eval_mul,Polynomial.eval_X,Polynomial.map_sum,Polynomial.eval_finset_sum,
      Rat.coe_castHom,Rat.cast_sub,Rat.cast_div,Rat.cast_intCast,bernsteinPolynomial,Polynomial.map_natCast,
      Polynomial.map_pow,Polynomial.map_sub,Polynomial.map_one,Polynomial.eval_pow,
      Polynomial.eval_natCast,Polynomial.eval_sub,Polynomial.eval_one] using hh
  have hh := cell_integral_abs_bound (p.map (Rat.castHom ℝ)) n (a:ℝ) (b:ℝ)
    (by exact_mod_cast hab) (fun i => (cs i:ℝ)/(S:ℝ)) (fun t ht => he t)
  have hSr : (0:ℝ) < S := by exact_mod_cast hS
  simp only [abs_div,abs_of_pos hSr,←Finset.sum_div] at hh
  simpa only [Rat.cast_sub,div_div,mul_div_assoc] using hh
end DusartLegendreSmoothing
#print axioms DusartLegendreSmoothing.cell_integral_abs_bound
#print axioms DusartLegendreSmoothing.partition_integral_abs_bound
#print axioms DusartLegendreSmoothing.rational_cell_integral_abs_bound


