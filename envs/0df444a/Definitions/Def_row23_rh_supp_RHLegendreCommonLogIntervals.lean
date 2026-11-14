-- Prove2me | Definitions.Def_row23_rh_supp_RHLegendreCommonLogIntervals
-- name    : row23_rh_supp_RHLegendreCommonLogIntervals
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:18:05.658484+00:00
-- url     : https://prove2.me/theorems/ead67131-5def-42b1-87a1-0f6410d3ed54
-- title:
--   Row 23 RH support: RHLegendreCommonLogIntervals
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendreScaledLog
import Definitions.Def_row23_rh_supp_RHLegendreLogCertificates_Batch01
import Definitions.Def_row23_rh_supp_RHLegendreLogCertificates_Batch02
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace DusartLegendreSmoothing.RationalMomentCaps
open RationalLog
def logPiLower : ℚ := 1837877066409345483/1000000000000000000
def logPiUpper : ℚ := 459469266602336371/250000000000000000
theorem pi_log_interval : (logPiLower:ℝ) ≤ Real.log (2*(piLower:ℝ)) ∧
    Real.log (2*(piUpper:ℝ)) ≤ (logPiUpper:ℝ) := by
  constructor
  · have h := RationalLog.log_pi2_lower.1
    norm_num [logPiLower,piLower] at h ⊢
    exact h
  · have h := RationalLog.log_pi2_upper.2
    norm_num [logPiUpper,piUpper] at h ⊢
    exact h
theorem scaled_logs_of_raw (a L U V : ℚ) (ha : 0 < a)
    (hlog : (L:ℝ) ≤ Real.log (a:ℝ) ∧ Real.log (a:ℝ) ≤ (U:ℝ))
    (hplus : Real.log ((a+5:ℚ):ℝ) ≤ (V:ℝ)) :
    ((L-logPiUpper:ℚ):ℝ) ≤ Real.log ((a:ℝ)/(2*Real.pi)) ∧
    Real.log ((a:ℝ)/(2*Real.pi)) ≤ ((U-logPiLower:ℚ):ℝ) ∧
    Real.log ((a:ℝ)+5) ≤ (V:ℝ) := by
  have haR : (0:ℝ) < a := by exact_mod_cast ha
  have hs := scaled_log_bounds (a:ℝ) (piLower:ℝ) (piUpper:ℝ) (L:ℝ) (U:ℝ)
    (logPiLower:ℝ) (logPiUpper:ℝ) haR pi_interval.1 pi_interval.2.1 pi_interval.2.2
    hlog.1 hlog.2 pi_log_interval.1 pi_log_interval.2
  refine ⟨?_,?_,?_⟩
  · simpa only [Rat.cast_sub] using hs.1
  · simpa only [Rat.cast_sub] using hs.2
  · push_cast at hplus
    exact hplus
theorem low_height_log_interval : (((12102053106984369201/1000000000000000000):ℚ):ℝ) ≤ Real.log ((lowHeight:ℝ)/(2*Real.pi)) ∧
    Real.log ((lowHeight:ℝ)/(2*Real.pi)) ≤ (((12102053106984369203/1000000000000000000):ℚ):ℝ) ∧
    Real.log ((lowHeight:ℝ)+5) ≤ (((6969967294215081279/500000000000000000):ℚ):ℝ) := by
  have hp := RationalLog.log_T0_plus5.2
  have h := scaled_logs_of_raw lowHeight (2787986034678742937/200000000000000000) (6969965086696857343/500000000000000000) (6969967294215081279/500000000000000000)
    (by norm_num [lowHeight]) (by simpa only [lowHeight] using RationalLog.log_T0)
    (by norm_num [lowHeight] at hp ⊢; exact hp)
  norm_num [logPiLower,logPiUpper] at h ⊢
  exact h
theorem high_height_log_interval : (((13343798952637790709/500000000000000000):ℚ):ℝ) ≤ Real.log ((highHeight:ℝ)/(2*Real.pi)) ∧
    Real.log ((highHeight:ℝ)/(2*Real.pi)) ≤ (((1334379895263779071/50000000000000000):ℚ):ℝ) ∧
    Real.log ((highHeight:ℝ)+5) ≤ (((28525474971686971057/1000000000000000000):ℚ):ℝ) := by
  have hp := RationalLog.log_H_plus5.2
  have h := scaled_logs_of_raw highHeight (14262737485842463451/500000000000000000) (28525474971684926903/1000000000000000000) (28525474971686971057/1000000000000000000)
    (by norm_num [highHeight]) (by simpa only [highHeight] using RationalLog.log_H)
    (by norm_num [highHeight] at hp ⊢; exact hp)
  norm_num [logPiLower,logPiUpper] at h ⊢
  exact h
end DusartLegendreSmoothing.RationalMomentCaps
#print axioms DusartLegendreSmoothing.RationalMomentCaps.low_height_log_interval
#print axioms DusartLegendreSmoothing.RationalMomentCaps.high_height_log_interval


