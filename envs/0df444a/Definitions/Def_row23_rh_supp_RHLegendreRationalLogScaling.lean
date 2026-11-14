-- Prove2me | Definitions.Def_row23_rh_supp_RHLegendreRationalLogScaling
-- name    : row23_rh_supp_RHLegendreRationalLogScaling
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:15:56.824653+00:00
-- url     : https://prove2.me/theorems/fceb5bf4-fcad-42a6-887c-8251c3d16319
-- title:
--   Row 23 RH support: RHLegendreRationalLogScaling
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendreRationalLog
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace DusartLegendreSmoothing.RationalLog
 def reduce (q : ℚ) (k : ℕ) : ℚ := q/(2:ℚ)^k
 def lower (q : ℚ) (k n : ℕ) : ℚ :=
  (k:ℚ)*seriesLower (1/3) n+seriesLower ((reduce q k-1)/(reduce q k+1)) n
 def upper (q : ℚ) (k n : ℕ) : ℚ :=
  (k:ℚ)*(seriesLower (1/3) n+tail (1/3) n)+
    (seriesLower ((reduce q k-1)/(reduce q k+1)) n+tail ((reduce q k-1)/(reduce q k+1)) n)
 theorem bounds (q : ℚ) (k n : ℕ) (hq : 1 ≤ reduce q k) :
    ((lower q k n:ℚ):ℝ) ≤ Real.log (q:ℝ) ∧
      Real.log (q:ℝ) ≤ ((upper q k n:ℚ):ℝ) := by
  have hz := unit_bounds (reduce q k) hq n
  have h2 := unit_bounds (2:ℚ) (by norm_num) n
  norm_num at h2
  have hred : (reduce q k:ℝ)=(q:ℝ)/(2:ℝ)^k := by
    unfold reduce
    push_cast
    rfl
  have hqR : (1:ℝ) ≤ (reduce q k:ℝ) := by exact_mod_cast hq
  have hred0 : (0:ℝ) < (reduce q k:ℝ) := lt_of_lt_of_le zero_lt_one hqR
  have hE : (q:ℝ)=(2:ℝ)^k*(reduce q k:ℝ) := by
    rw [hred]
    field_simp
  have hlog : Real.log (q:ℝ)=(k:ℝ)*Real.log 2+Real.log (reduce q k:ℝ) := by
    calc
      _ = Real.log ((2:ℝ)^k*(reduce q k:ℝ)) := congrArg Real.log hE
      _ = Real.log ((2:ℝ)^k)+Real.log (reduce q k:ℝ) :=
        Real.log_mul (by positivity) hred0.ne'
      _ = _ := by rw [Real.log_pow]
  constructor
  · dsimp only [lower]
    push_cast
    have hL := add_le_add (mul_le_mul_of_nonneg_left h2.1 (Nat.cast_nonneg k)) hz.1
    exact hL.trans_eq hlog.symm
  · rw [Rat.cast_add] at hz
    dsimp only [upper]
    push_cast
    have hU := add_le_add (mul_le_mul_of_nonneg_left h2.2 (Nat.cast_nonneg k)) hz.2
    exact hlog.le.trans hU
end DusartLegendreSmoothing.RationalLog
#print axioms DusartLegendreSmoothing.RationalLog.bounds


