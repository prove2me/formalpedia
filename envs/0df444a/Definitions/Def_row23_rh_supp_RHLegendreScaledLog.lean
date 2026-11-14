-- Prove2me | Definitions.Def_row23_rh_supp_RHLegendreScaledLog
-- name    : row23_rh_supp_RHLegendreScaledLog
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:16:56.987535+00:00
-- url     : https://prove2.me/theorems/26671b76-75cf-4680-8606-fd48da0f0aa6
-- title:
--   Row 23 RH support: RHLegendreScaledLog
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendreRationalLogCertificate
import Definitions.Def_row23_rh_supp_RHLegendreMomentCapModel
import Mathlib.Analysis.Real.Pi.Bounds
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace DusartLegendreSmoothing.RationalMomentCaps
 theorem pi_interval : (0:ℝ) < piLower ∧ (piLower:ℝ) ≤ Real.pi ∧ Real.pi ≤ (piUpper:ℝ) := by
  refine ⟨by norm_num [piLower],?_,?_⟩
  · have h := Real.pi_gt_d20.le
    norm_num [piLower] at h ⊢
    exact h
  · have h := Real.pi_lt_d20.le
    norm_num [piUpper] at h ⊢
    exact h
 theorem scaled_log_bounds (a PL PU L U R S : ℝ)
    (ha : 0 < a) (hPL : 0 < PL) (hPlo : PL ≤ Real.pi) (hPhi : Real.pi ≤ PU)
    (haLo : L ≤ Real.log a) (haHi : Real.log a ≤ U)
    (hpiLo : R ≤ Real.log (2*PL)) (hpiHi : Real.log (2*PU) ≤ S) :
    L-S ≤ Real.log (a/(2*Real.pi)) ∧ Real.log (a/(2*Real.pi)) ≤ U-R := by
  have hLo : Real.log (2*PL) ≤ Real.log (2*Real.pi) :=
    Real.log_le_log (by positivity) (by linarith)
  have hHi : Real.log (2*Real.pi) ≤ Real.log (2*PU) :=
    Real.log_le_log (by positivity) (by linarith)
  rw [Real.log_div ha.ne' (by positivity : 2*Real.pi ≠ 0)]
  constructor <;> linarith
end DusartLegendreSmoothing.RationalMomentCaps
#print axioms DusartLegendreSmoothing.RationalMomentCaps.scaled_log_bounds


