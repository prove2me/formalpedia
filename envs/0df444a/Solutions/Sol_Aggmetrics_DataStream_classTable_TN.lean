-- Prove2me | solution 1 for Aggmetrics.DataStream.classTable_TN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:04:05.362179+00:00
-- url     : https://prove2.me/submissions/7ecba597-98e4-4d1c-8b69-ffc41ba51f96

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal
import Theorems.Thm_Aggmetrics_DataStream_classTable_apply
import Theorems.Thm_Aggmetrics_DataStream_sel_one
import Theorems.Thm_Aggmetrics_DataStream_sum_ne_mul

set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {m : ℕ} (C : Matrix (Fin m) (Fin m) ℝ) (j : Fin m) :
    classTable C j 1 1 = ∑ a ∈ univ.erase j, ∑ b ∈ univ.erase j, C a b := by
  rw [classTable_apply]
  have : ∀ b, (∑ a, sel j 1 a * C a b) = ∑ a ∈ univ.erase j, C a b := fun b => by
    simp only [sel_one]
    exact sum_ne_mul (fun a => C a b) j
  simp only [this]
  simp only [sel_one]
  rw [show (∑ b, (∑ a ∈ univ.erase j, C a b) * (if b = j then (0 : ℝ) else 1))
      = ∑ b, (if b = j then (0 : ℝ) else 1) * ∑ a ∈ univ.erase j, C a b from
        Finset.sum_congr rfl fun b _ => mul_comm _ _,
    sum_ne_mul (fun b => ∑ a ∈ univ.erase j, C a b) j]
  exact Finset.sum_comm
end Aggmetrics.DataStream
