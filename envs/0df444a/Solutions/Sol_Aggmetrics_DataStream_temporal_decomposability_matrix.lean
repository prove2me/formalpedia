-- Prove2me | solution 1 for Aggmetrics.DataStream.temporal_decomposability_matrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:05:41.176912+00:00
-- url     : https://prove2.me/submissions/20977720-ace0-4c78-9943-fc243ad2bc62

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal
import Theorems.Thm_Aggmetrics_DataStream_weighted_ratio_mixture_nonneg
import Theorems.Thm_Aggmetrics_DataStream_classTable_nonneg
import Theorems.Thm_Aggmetrics_DataStream_lin_sum
import Theorems.Thm_Aggmetrics_DataStream_lin_nonneg
import Theorems.Thm_Aggmetrics_DataStream_lin_le

set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {m : ℕ} (C : Matrix (Fin m) (Fin m) ℝ)
    (hC : ∀ a b, 0 ≤ C a b) (a b : Fin 4 → ℝ) (ha : ∀ i, 0 ≤ a i) (hab : ∀ i, a i ≤ b i)
    (hpos : 0 < ∑ j, lin b (classTable C j)) :
    measure a b (∑ j, classTable C j)
      = ∑ j, (lin b (classTable C j) / ∑ l, lin b (classTable C l))
          * measure a b (classTable C j) := by
  unfold measure
  rw [lin_sum, lin_sum]
  refine weighted_ratio_mixture_nonneg (fun j => lin a (classTable C j))
    (fun j => lin b (classTable C j)) (fun j hj => ?_) hpos
  have h0 := lin_nonneg ha (classTable_nonneg hC j)
  have h1 := lin_le hab (classTable_nonneg hC j)
  have hj' : lin b (classTable C j) = 0 := hj
  show lin a (classTable C j) = 0
  linarith
end Aggmetrics.DataStream
