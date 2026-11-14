-- Prove2me | Definitions.Def_row23_rh_supp_RHLegendreLogPowerIntegral
-- name    : row23_rh_supp_RHLegendreLogPowerIntegral
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:00:07.341718+00:00
-- url     : https://prove2.me/theorems/3852719a-9f47-41ba-9bc3-05a73a0ee567
-- title:
--   Row 23 RH support: RHLegendreLogPowerIntegral
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendreCountEnvelope
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace DusartLegendreSmoothing
open Set MeasureTheory
lemma log_scaled_hasDerivAt (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun u : ℝ => Real.log (u/(2*Real.pi))) (1/t) t := by
  have h := (Real.hasDerivAt_log (div_ne_zero ht.ne' (by positivity : 2*Real.pi ≠ 0))).comp t
    ((hasDerivAt_id t).div_const (2*Real.pi))
  apply h.congr_deriv
  field_simp [ht.ne',Real.pi_ne_zero]
noncomputable def logPowerPrimitive (k : ℕ) (t : ℝ) : ℝ :=
  -(1+((k:ℝ)+1)*Real.log (t/(2*Real.pi)))/(((k:ℝ)+1)^2*t^(k+1))
 theorem logPowerPrimitive_hasDerivAt (k : ℕ) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (logPowerPrimitive k)
      (Real.log (t/(2*Real.pi))/t^(k+2)) t := by
  have hm : (k:ℝ)+1 ≠ 0 := by positivity
  have hn := ((log_scaled_hasDerivAt t ht).const_mul ((k:ℝ)+1)).const_add 1
  have hd := ((hasDerivAt_id t).pow (k+1)).const_mul (((k:ℝ)+1)^2)
  have hden : ((k:ℝ)+1)^2*t^(k+1) ≠ 0 := by positivity
  have h := (hn.neg.div hd hden)
  change HasDerivAt (logPowerPrimitive k) _ t at h
  apply h.congr_deriv
  simp only [Pi.pow_apply,Pi.neg_apply,id_eq,Nat.add_sub_cancel,mul_one]
  push_cast
  field_simp [ht.ne',hm]
  <;> simp only [pow_succ]
  <;> ring
lemma continuousOn_log_div_pow (n : ℕ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ContinuousOn (fun t : ℝ => Real.log (t/(2*Real.pi))/t^n) (uIcc a b) := by
  have hpos (t : ℝ) (ht : t ∈ uIcc a b) : 0 < t := by
    rw [uIcc_of_le hab] at ht
    exact ha.trans_le ht.1
  have hl : ContinuousOn (fun t : ℝ => Real.log (t/(2*Real.pi))) (uIcc a b) :=
    (continuousOn_id.div_const (2*Real.pi)).log (fun t ht =>
      div_ne_zero (hpos t ht).ne' (by positivity))
  exact hl.div (continuousOn_id.pow n) (fun t ht => pow_ne_zero n (hpos t ht).ne')
 theorem integral_log_div_pow (k : ℕ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ t : ℝ in a..b, Real.log (t/(2*Real.pi))/t^(k+2)) =
      (1+((k:ℝ)+1)*Real.log (a/(2*Real.pi)))/(((k:ℝ)+1)^2*a^(k+1))-
      (1+((k:ℝ)+1)*Real.log (b/(2*Real.pi)))/(((k:ℝ)+1)^2*b^(k+1)) := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => logPowerPrimitive_hasDerivAt k t (by
      rw [uIcc_of_le hab] at ht
      exact ha.trans_le ht.1)) (continuousOn_log_div_pow (k+2) a b ha hab).intervalIntegrable
  exact h.trans (by unfold logPowerPrimitive; ring)
 theorem integral_log_div_self (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ t : ℝ in a..b, Real.log (t/(2*Real.pi))/t) =
      ((Real.log (b/(2*Real.pi)))^2-(Real.log (a/(2*Real.pi)))^2)/2 := by
  have hd (t : ℝ) (ht : 0 < t) :
      HasDerivAt (fun u : ℝ => (1/2:ℝ)*(Real.log (u/(2*Real.pi)))^2)
        (Real.log (t/(2*Real.pi))/t) t := by
    have h := ((log_scaled_hasDerivAt t ht).pow 2).const_mul (1/2:ℝ)
    apply h.congr_deriv
    simp only [Pi.pow_apply,id_eq,Nat.reduceSub,pow_one]
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd t (by rw [uIcc_of_le hab] at ht; exact ha.trans_le ht.1))
    (by simpa only [pow_one] using (continuousOn_log_div_pow 1 a b ha hab).intervalIntegrable)
  exact h.trans (by ring)
end DusartLegendreSmoothing
#print axioms DusartLegendreSmoothing.integral_log_div_pow
#print axioms DusartLegendreSmoothing.integral_log_div_self


