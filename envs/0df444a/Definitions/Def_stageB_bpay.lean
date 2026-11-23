-- Prove2me | Definitions.Def_stageB_bpay
-- name    : stageB_bpay
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-23T00:03:03.940629+00:00
-- url     : https://prove2.me/theorems/e86cecde-05a8-4a22-a11c-85962cb20bb7
-- title:
--   stageB_bpay
-- statement:
--   Automatically extracted helper definition stageB_bpay from oversized parent candidate 8c694b057acd248e08af038d68cb321f7cf2ffcb0fb7618f8d38cc1f8d3d502f.
-- source:
--   candidate-decomposition:47fdba96-7849-46b6-87b0-6cea26c5eadd:8c694b057acd248e08af038d68cb321f7cf2ffcb0fb7618f8d38cc1f8d3d502f

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_filtered_avram_model
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_positive_open_clock_eq_all_times
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_uncapped_reflected_killed_future_reward_factor
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_fresh_reflected_reward_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_origin_sampled_reflected_reward_eq_true
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_shifted_sampled_reward_true_pair
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_two_record_discount_pathwise
import Theorems.Thm_AvramDividend_Classical_levyPath_bddAbove_Icc
import Theorems.Thm_AvramDividend_Classical_shiftedSup_increment_eq_sup_sub
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_runningSup_sub_path_eq_zero
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_before_barrierRuin_iff_prefix_survival
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_strictly_before_drawdown_ruin
import Theorems.Thm_AvramDividend_Classical_reflectedSup_upperSemicontinuousOn_Icc
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_mono_barrier
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_measurable
import Theorems.Thm_AvramDividend_Classical_upperPassage_measurable_from_stopping
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable def stageB_bpay {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (d b q : ℝ) (ω : Ω) : ℝ≥0∞ :=
  if twoSidedExitUpTime X b ω < barrierRuinTime X d ω then ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X b ω).toReal))) else 0


