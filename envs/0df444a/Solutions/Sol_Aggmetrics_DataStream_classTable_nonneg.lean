-- Prove2me | solution 1 for Aggmetrics.DataStream.classTable_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:02:27.500816+00:00
-- url     : https://prove2.me/submissions/245b8107-d087-478d-93fe-d9fb7824faf2

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal
import Theorems.Thm_Aggmetrics_DataStream_sel_nonneg

set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {m : ℕ} {C : Matrix (Fin m) (Fin m) ℝ} (hC : ∀ a b, 0 ≤ C a b)
    (j : Fin m) (r s : Fin 2) : 0 ≤ classTable C j r s := by
  simp only [classTable, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_nonneg fun b _ =>
    mul_nonneg (Finset.sum_nonneg fun a _ => mul_nonneg (sel_nonneg j r a) (hC a b)) (sel_nonneg j s b)
end Aggmetrics.DataStream
