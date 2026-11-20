-- Prove2me | solution 1 for Aggmetrics.DataStream.classTable_FP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:04:02.497707+00:00
-- url     : https://prove2.me/submissions/973c6c4f-6d85-401e-b1a9-1ed2fa9defd6

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
    classTable C j 1 0 = ∑ a ∈ univ.erase j, C a j := by
  rw [classTable_apply]
  have : ∀ b, (∑ a, sel j 1 a * C a b) = ∑ a ∈ univ.erase j, C a b := fun b => by
    simp only [sel_one]
    exact sum_ne_mul (fun a => C a b) j
  simp only [this, sel_zero]
  simp
end Aggmetrics.DataStream
