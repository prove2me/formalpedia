-- Prove2me | solution 1 for Aggmetrics.DataStream.classTable_FN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:03:33.391539+00:00
-- url     : https://prove2.me/submissions/3c2fc58a-5484-482e-8476-9ee22d473546

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal
import Theorems.Thm_Aggmetrics_DataStream_classTable_apply
import Theorems.Thm_Aggmetrics_DataStream_sel_zero
import Theorems.Thm_Aggmetrics_DataStream_sel_one
import Theorems.Thm_Aggmetrics_DataStream_sum_ne_mul

set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {m : ℕ} (C : Matrix (Fin m) (Fin m) ℝ) (j : Fin m) :
    classTable C j 0 1 = ∑ b ∈ univ.erase j, C j b := by
  rw [classTable_apply]
  have : ∀ b, (∑ a, sel j 0 a * C a b) = C j b := fun b => by simp [sel_zero]
  simp only [this, sel_one]
  rw [← sum_ne_mul (fun b => C j b) j]
  exact Finset.sum_congr rfl fun b _ => mul_comm _ _
end Aggmetrics.DataStream
