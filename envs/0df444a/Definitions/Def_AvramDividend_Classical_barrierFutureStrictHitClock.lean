-- Prove2me | Definitions.Def_AvramDividend_Classical_barrierFutureStrictHitClock
-- name    : AvramDividend_Classical_barrierFutureStrictHitClock
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T17:41:22.900732+00:00
-- url     : https://prove2.me/theorems/8855a885-eab6-4455-b89f-179117ebf255
-- title:
--   AvramDividend.Classical.barrierFutureStrictHitClock
-- statement:
--   Automatically extracted helper definition AvramDividend.Classical.barrierFutureStrictHitClock from oversized parent candidate fcf98695524a14362cf237ed3c29b7b2eaafbdd6d99f2ab37359f5ac0a5c4003.
-- source:
--   candidate-decomposition:8fc83520-78bb-4a8c-a394-12b04a096b66:fcf98695524a14362cf237ed3c29b7b2eaafbdd6d99f2ab37359f5ac0a5c4003

import Mathlib
import Theorems.Thm_AvramDividend_Classical_levyPath_bddAbove_Icc
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_ruinTime_post_firstUpcrossing_add_shifted_badClock
import Theorems.Thm_AvramDividend_Classical_shiftedSup_dividendMeasure_zero_nonpositive_of_levy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_barrierValue_self_eq_barrierSupValue
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_killedDiscount_futureReward_factor_rightCont
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedFuturePath_measurable
import Theorems.Thm_AvramDividend_Classical_firstBadClock_shift_of_no_early_breach
import Theorems.Thm_AvramDividend_Classical_riskProcess_post_firstUpcrossing_ruin_iff
import Theorems.Thm_AvramDividend_Classical_dividendValue_barrierStrategy_expected_shifted_stoppedReward
open MeasureTheory Set
open scoped NNReal ENNReal
namespace AvramDividend.Classical

noncomputable def barrierFutureStrictHitClock
    (b : ℝ) (f : ℝ≥0 → ℝ) : ℝ≥0∞ :=
  ⨅ r : ℚ≥0, if b < f (r : ℝ≥0) then (r : ℝ≥0∞) else ⊤
end AvramDividend.Classical


