-- Prove2me | solution 1 for Aggmetrics.DataStream.evict_age_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:27:35.754925+00:00
-- url     : https://prove2.me/submissions/28e1cede-b4c9-41a8-96b8-d5cad0c13a50

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamEviction
import Theorems.Thm_Aggmetrics_DataStream_window_sizing_rule


set_option autoImplicit true
open Finset Matrix
open scoped Classical
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {α ε : ℝ} (h0 : 0 < α) (h1 : α < 1) (hε : 0 < ε) :
    ∃ N : ℕ, (1 - α) * α ^ N < ε ∧
      (N : ℝ) ≤ max (Real.log ((1 - α) / ε)) 0 / (1 - α) + 2 := by
  have hpos : 0 < 1 - α := by linarith
  set x := Real.log ((1 - α) / ε) / (-Real.log α) with hx
  have hlogα : Real.log α < 0 := Real.log_neg h0 h1
  refine ⟨⌈x⌉₊ + 1, ?_, ?_⟩
  · have hW : ((⌈x⌉₊ : ℕ) : ℝ) ≥ Real.log (1 / (ε / (1 - α))) / (-Real.log (1 - (1 - α))) := by
      rw [one_div_div, sub_sub_cancel]
      exact Nat.le_ceil x
    have hsz := window_sizing_rule (1 - α) (ε / (1 - α)) hpos (by linarith)
      (div_pos hε hpos) ⌈x⌉₊ hW
    rw [sub_sub_cancel] at hsz
    have h3 : α ^ (⌈x⌉₊ + 1) < ε / (1 - α) := by
      refine lt_of_lt_of_le ?_ hsz
      rw [pow_succ]
      nlinarith [pow_pos h0 ⌈x⌉₊]
    calc (1 - α) * α ^ (⌈x⌉₊ + 1) < (1 - α) * (ε / (1 - α)) :=
          mul_lt_mul_of_pos_left h3 hpos
      _ = ε := by field_simp
  · push_cast
    by_cases hxn : x ≤ 0
    · have : ⌈x⌉₊ = 0 := Nat.ceil_eq_zero.mpr hxn
      rw [this]
      have : 0 ≤ max (Real.log ((1 - α) / ε)) 0 / (1 - α) := by positivity
      simp only [Nat.cast_zero]
      linarith
    · push_neg at hxn
      have hceil := Nat.ceil_lt_add_one hxn.le
      have hL : 0 < Real.log ((1 - α) / ε) := by
        by_contra hnot
        push_neg at hnot
        have : x ≤ 0 := div_nonpos_of_nonpos_of_nonneg hnot (by linarith)
        linarith
      have hle : 1 - α ≤ -Real.log α := by
        have := Real.log_le_sub_one_of_pos h0
        linarith
      have hxle : x ≤ Real.log ((1 - α) / ε) / (1 - α) :=
        div_le_div_of_nonneg_left hL.le hpos hle
      rw [max_eq_left hL.le]
      linarith
end Aggmetrics.DataStream
