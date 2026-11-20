-- Prove2me | solution 1 for Aggmetrics.DataStream.micro_change_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:08:24.18219+00:00
-- url     : https://prove2.me/submissions/bff700fd-b224-41a2-a1f9-da021d45b40d

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal
import Theorems.Thm_Aggmetrics_DataStream_temporal_decomposability_matrix
import Theorems.Thm_Aggmetrics_DataStream_discrete_decomposition

set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {m : ℕ} (C0 C1 : Matrix (Fin m) (Fin m) ℝ)
    (hC0 : ∀ a b, 0 ≤ C0 a b) (hC1 : ∀ a b, 0 ≤ C1 a b)
    (a b : Fin 4 → ℝ) (ha : ∀ i, 0 ≤ a i) (hab : ∀ i, a i ≤ b i)
    (hpos0 : 0 < ∑ j, lin b (classTable C0 j)) (hpos1 : 0 < ∑ j, lin b (classTable C1 j)) :
    measure a b (∑ j, classTable C1 j) - measure a b (∑ j, classTable C0 j)
      = ∑ j, ((omega b C0 j + omega b C1 j) / 2)
            * (measure a b (classTable C1 j) - measure a b (classTable C0 j))
        + ∑ j, (omega b C1 j - omega b C0 j)
            * ((measure a b (classTable C0 j) + measure a b (classTable C1 j)) / 2) := by
  rw [temporal_decomposability_matrix C1 hC1 a b ha hab hpos1,
    temporal_decomposability_matrix C0 hC0 a b ha hab hpos0, ← Finset.sum_sub_distrib]
  exact discrete_decomposition (omega b C0) (omega b C1)
    (fun j => measure a b (classTable C0 j)) (fun j => measure a b (classTable C1 j))
end Aggmetrics.DataStream
