-- Prove2me | Definitions.Def_row23_rh_supp_RHLegendreRationalLog
-- name    : row23_rh_supp_RHLegendreRationalLog
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:15:33.924248+00:00
-- url     : https://prove2.me/theorems/0581ca96-db7d-4aa5-a22f-7a2518bd2c60
-- title:
--   Row 23 RH support: RHLegendreRationalLog
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace DusartLegendreSmoothing.RationalLog
open Finset
 def seriesLower (x : ℚ) (n : ℕ) : ℚ :=
  2*∑ i ∈ range n, x^(2*i+1)/((2*i+1:ℕ):ℚ)
 def tail (x : ℚ) (n : ℕ) : ℚ := 2*(x^(2*n+1)/(1-x^2))
 lemma cast_seriesLower (x : ℚ) (n : ℕ) :
    ((seriesLower x n:ℚ):ℝ)=2*∑ i ∈ range n, (x:ℝ)^(2*i+1)/((2*i+1:ℕ):ℝ) := by
  unfold seriesLower
  push_cast
  rfl
 lemma cast_tail (x : ℚ) (n : ℕ) :
    ((tail x n:ℚ):ℝ)=2*((x:ℝ)^(2*n+1)/(1-(x:ℝ)^2)) := by
  unfold tail
  push_cast
  rfl
 theorem unit_bounds (q : ℚ) (hq : 1 ≤ q) (n : ℕ) :
    ((seriesLower ((q-1)/(q+1)) n:ℚ):ℝ) ≤ Real.log (q:ℝ) ∧
    Real.log (q:ℝ) ≤ ((seriesLower ((q-1)/(q+1)) n+tail ((q-1)/(q+1)) n:ℚ):ℝ) := by
  have hqR : (1:ℝ) ≤ q := by exact_mod_cast hq
  let x : ℚ := (q-1)/(q+1)
  have hxR : (x:ℝ)=((q:ℝ)-1)/((q:ℝ)+1) := by
    dsimp only [x]
    push_cast
    rfl
  have hx0 : (0:ℝ) ≤ x := by rw [hxR]; positivity
  have hx1 : (x:ℝ) < 1 := by
    rw [hxR]
    apply (div_lt_iff₀ (by linarith : (0:ℝ) < (q:ℝ)+1)).2
    linarith
  have he : ((1:ℝ)+(x:ℝ))/(1-(x:ℝ))=(q:ℝ) := by
    rw [hxR]
    field_simp [show (q:ℝ)+1 ≠ 0 by linarith]
    <;> ring
  have hL := Real.sum_range_le_log_div hx0 hx1 n
  have hU := Real.log_div_le_sum_range_add hx0 hx1 n
  rw [he] at hL hU
  constructor
  · rw [cast_seriesLower]
    change 2*(∑ i ∈ range n, (x:ℝ)^(2*i+1)/((2*i+1:ℕ):ℝ)) ≤ _
    norm_num only [Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat]
    linarith only [hL]
  · rw [Rat.cast_add,cast_seriesLower,cast_tail]
    change _ ≤ 2*(∑ i ∈ range n, (x:ℝ)^(2*i+1)/((2*i+1:ℕ):ℝ))+
      2*((x:ℝ)^(2*n+1)/(1-(x:ℝ)^2))
    norm_num only [Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat]
    linarith only [hU]
end DusartLegendreSmoothing.RationalLog
#print axioms DusartLegendreSmoothing.RationalLog.unit_bounds


