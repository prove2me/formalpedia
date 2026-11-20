-- Prove2me | solution 1 for Aggmetrics.DataStream.fadeState_eq_state
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:05:55.660116+00:00
-- url     : https://prove2.me/submissions/b40ae857-dcec-4ebf-81d5-489d905c589d

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal
import Theorems.Thm_Aggmetrics_DataStream_fadeState_eq_sum

set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {m : ℕ} (α : ℝ) (y p : ℕ → Fin m → ℝ) (n : ℕ) :
    fadeState α y p n
      = state (fun k : Fin n => fadeWeight α n k) (fun k => y k) (fun k => p k) := by
  rw [fadeState_eq_sum]
  unfold state
  exact (Fin.sum_univ_eq_sum_range (fun k => fadeWeight α n k • outer (y k) (p k)) n).symm
end Aggmetrics.DataStream
