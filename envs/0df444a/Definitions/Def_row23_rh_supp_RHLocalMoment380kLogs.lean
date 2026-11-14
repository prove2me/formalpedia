-- Prove2me | Definitions.Def_row23_rh_supp_RHLocalMoment380kLogs
-- name    : row23_rh_supp_RHLocalMoment380kLogs
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:20:04.592724+00:00
-- url     : https://prove2.me/theorems/0ab09a5c-74b2-4aa2-aab3-d7d2b4909f44
-- title:
--   Row 23 RH support: RHLocalMoment380kLogs
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLocalMoment380kReal
import Definitions.Def_row23_rh_supp_RHLocalMoment380kArithmetic
import Definitions.Def_row23_rh_supp_RHLegendreCommonLogIntervals
import Definitions.Def_row23_rh_supp_RHLocalLog500kRaw0
import Definitions.Def_row23_rh_supp_RHLocalLog500kRaw1
import Definitions.Def_row23_rh_supp_RHLocalLog380kRaw
set_option autoImplicit false
set_option maxHeartbeats 10000000
namespace DusartLegendreSmoothing.Moment380k

theorem d23_logBounds : logBounds p23 d23 := by
  have h0 := RationalMomentCaps.scaled_logs_of_raw (1000:ℚ) (6907/1000) (6909/1000) 7
    (by norm_num) RHLocalLog500k.log1000 (by norm_num; exact RHLocalLog500k.log1005.2)
  have hT := RationalMomentCaps.scaled_logs_of_raw (92500:ℚ) (114348/10000) (114352/10000) (114352/10000)
    (by norm_num) RHLocalLog380k.log92500 (by have h := RHLocalLog380k.log92505.2; norm_num at h ⊢; exact h)
  have hH := RationalMomentCaps.scaled_logs_of_raw (380000:ℚ) (128478/10000) (128481/10000) (128481/10000)
    (by norm_num) RHLocalLog380k.log380000 (by have h := RHLocalLog380k.log380005.2; norm_num at h ⊢; exact h)
  unfold logBounds
  norm_num [p23,d23,lowHeight,highHeight,RationalMomentCaps.logPiLower,RationalMomentCaps.logPiUpper] at h0 hT hH ⊢
  rcases h0 with ⟨h01,h02,h03⟩
  rcases hT with ⟨hT1,hT2,hT3⟩
  rcases hH with ⟨hH1,hH2,hH3⟩
  constructor; · linarith
  constructor; · linarith
  constructor; · linarith
  constructor; · linarith
  constructor; · linarith
  constructor; · linarith
  constructor; · linarith
  constructor; · linarith
  linarith
end DusartLegendreSmoothing.Moment380k
#print axioms DusartLegendreSmoothing.Moment380k.d23_logBounds


