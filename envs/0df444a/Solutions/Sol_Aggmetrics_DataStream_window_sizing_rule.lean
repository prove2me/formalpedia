-- Prove2me | solution 1 for Aggmetrics.DataStream.window_sizing_rule
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:02:51.25867+00:00
-- url     : https://prove2.me/submissions/f4fccbb0-51e2-405f-b05d-08e10ea811d7

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStream

set_option autoImplicit true
open Finset MeasureTheory
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution (p δ : ℝ) (hp1 : 0 < p) (hp2 : p < 1) (hδ : 0 < δ)
    (W : ℕ) (hW : (W : ℝ) ≥ Real.log (1 / δ) / (-Real.log (1 - p))) :
    (1 - p) ^ W ≤ δ := by
  have h1p_pos : 0 < 1 - p := by linarith
  have h1p_lt1 : 1 - p < 1 := by linarith
  have hlog_neg : Real.log (1 - p) < 0 := Real.log_neg h1p_pos h1p_lt1
  have hL_pos : 0 < -Real.log (1 - p) := by linarith
  rw [ge_iff_le, div_le_iff₀ hL_pos] at hW
  have hinv_log : Real.log (1 / δ) = -Real.log δ := by rw [one_div, Real.log_inv]
  rw [hinv_log] at hW
  have hring : (W : ℝ) * (-Real.log (1 - p)) = -((W : ℝ) * Real.log (1 - p)) := by ring
  rw [hring] at hW
  have hpow_log : Real.log ((1 - p) ^ W) = (W : ℝ) * Real.log (1 - p) := Real.log_pow (1 - p) W
  have key : Real.log ((1 - p) ^ W) ≤ Real.log δ := by
    rw [hpow_log]; linarith [hW]
  have hpow_pos : 0 < (1 - p) ^ W := pow_pos h1p_pos W
  have hexp := Real.exp_le_exp.mpr key
  rwa [Real.exp_log hpow_pos, Real.exp_log hδ] at hexp
end Aggmetrics.DataStream
