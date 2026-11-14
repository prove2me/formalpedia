-- Prove2me | Definitions.Def_row23_rh_supp_RHLegendreFiniteZeroMoments
-- name    : row23_rh_supp_RHLegendreFiniteZeroMoments
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:01:00.746843+00:00
-- url     : https://prove2.me/theorems/a8f8e512-91f7-4ec9-a56b-a9a694351327
-- title:
--   Row 23 RH support: RHLegendreFiniteZeroMoments
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendreSmoothCountEnvelope
import Definitions.Def_row23_rh_supp_RHLegendreLogPowerIntegral
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace DusartLegendreSmoothing
open DusartSmoothing Set MeasureTheory
 theorem smoothCountEnvelope_hasDerivAt (a t : ℝ) (ht : 0 < t) :
    HasDerivAt (smoothCountEnvelope a) (zeroCountSlope a*Real.log (t/(2*Real.pi))) t := by
  have h := (((RvM.hasDerivAt_countingMain t ht).sub_const (RvM.countingMain a)).const_mul
    (2*Real.pi*zeroCountSlope a)).add_const (2*(9*Real.log (a+5)+79))
  change HasDerivAt (smoothCountEnvelope a) _ t at h
  apply h.congr_deriv
  field_simp [Real.pi_ne_zero]
  <;> ring
 theorem inversePower_hasDerivAt (n : ℕ) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun u : ℝ => 1/u^(n+1)) (-((n:ℝ)+1)/t^(n+2)) t := by
  have h := (hasDerivAt_const t (1:ℝ)).div ((hasDerivAt_id t).pow (n+1))
    (pow_ne_zero _ ht.ne')
  change HasDerivAt (fun u : ℝ => 1/u^(n+1)) _ t at h
  apply h.congr_deriv
  simp only [Pi.pow_apply,id_eq,Nat.add_sub_cancel,mul_one,zero_mul,zero_sub,one_mul]
  push_cast
  field_simp [ht.ne']
  <;> simp only [pow_succ]
  <;> ring
 theorem finite_positive_zero_power_density_bound (n : ℕ) (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (a b : ℝ) (ha : 1000 ≤ a) (hab : a ≤ b)
    (hγ : ∀ ρ ∈ Z, a < ρ.im ∧ ρ.im ≤ b) :
    (∑ ρ ∈ Z, (RvM.zeroMult ρ:ℝ)*(1/ρ.im^(n+1))) ≤
      2*(9*Real.log (a+5)+79)/a^(n+1)+
      zeroCountSlope a*(∫ t : ℝ in a..b, Real.log (t/(2*Real.pi))/t^(n+1)) := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := ha0.trans_le hab
  have hpos (t : ℝ) (ht : t ∈ Icc a b) : 0 < t := ha0.trans_le ht.1
  have hgp : ContinuousOn (fun t : ℝ => -((n:ℝ)+1)/t^(n+2)) (Icc a b) :=
    continuousOn_const.div (continuousOn_id.pow _) (fun t ht => pow_ne_zero _ (hpos t ht).ne')
  have hFp : ContinuousOn (fun t : ℝ => zeroCountSlope a*Real.log (t/(2*Real.pi))) (Icc a b) := by
    have hl : ContinuousOn (fun t : ℝ => Real.log (t/(2*Real.pi))) (Icc a b) :=
      (continuousOn_id.div_const (2*Real.pi)).log (fun t ht =>
        div_ne_zero (hpos t ht).ne' (by positivity))
    exact hl.const_mul _
  have hB := finite_zero_sum_le_count_envelope Z RvM.zeroMult Complex.im a b hab
    (fun ρ hρ => ⟨(hγ ρ hρ).1.le,(hγ ρ hρ).2⟩)
    (fun t : ℝ => 1/t^(n+1)) (fun t : ℝ => -((n:ℝ)+1)/t^(n+2))
    (smoothCountEnvelope a) (fun t : ℝ => zeroCountSlope a*Real.log (t/(2*Real.pi)))
    hgp hFp (fun t ht => inversePower_hasDerivAt n t (hpos t ht))
    (fun t ht => smoothCountEnvelope_hasDerivAt a t (hpos t ht)) (by positivity)
    (fun t ht => div_nonpos_of_nonpos_of_nonneg (by have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith)
      (pow_nonneg (hpos t ht).le _))
    (fun t ht => finite_zero_count_smooth_envelope Z hZ a t ha ht.1 (fun ρ hρ => (hγ ρ hρ).1))
  apply hB.trans_eq
  have he : (fun t : ℝ => (1/t^(n+1))*(zeroCountSlope a*Real.log (t/(2*Real.pi)))) =
      fun t : ℝ => zeroCountSlope a*(Real.log (t/(2*Real.pi))/t^(n+1)) := by
    funext t
    ring
  rw [he,intervalIntegral.integral_const_mul]
  simp only [smoothCountEnvelope,sub_self,mul_zero,zero_add]
  ring
 theorem finite_positive_zero_moment_band (k : ℕ) (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (a b : ℝ) (ha : 1000 ≤ a) (hab : a ≤ b)
    (hγ : ∀ ρ ∈ Z, a < ρ.im ∧ ρ.im ≤ b) :
    (∑ ρ ∈ Z, (RvM.zeroMult ρ:ℝ)*(1/ρ.im^(k+2))) ≤
      2*(9*Real.log (a+5)+79)/a^(k+2)+zeroCountSlope a*
      ((1+((k:ℝ)+1)*Real.log (a/(2*Real.pi)))/(((k:ℝ)+1)^2*a^(k+1))-
       (1+((k:ℝ)+1)*Real.log (b/(2*Real.pi)))/(((k:ℝ)+1)^2*b^(k+1))) := by
  have h := finite_positive_zero_power_density_bound (k+1) Z hZ a b ha hab hγ
  norm_num only [show k+1+1=k+2 by omega] at h
  rw [integral_log_div_pow k a b (by linarith) hab] at h
  exact h
end DusartLegendreSmoothing
#print axioms DusartLegendreSmoothing.finite_positive_zero_moment_band


