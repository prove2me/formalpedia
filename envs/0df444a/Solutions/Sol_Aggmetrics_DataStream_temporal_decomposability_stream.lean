-- Prove2me | solution 1 for Aggmetrics.DataStream.temporal_decomposability_stream
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:08:23.564815+00:00
-- url     : https://prove2.me/submissions/cd16a9ea-b324-4e2b-a202-57788c57d8a3

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal
import Theorems.Thm_Aggmetrics_DataStream_state_nonneg
import Theorems.Thm_Aggmetrics_DataStream_temporal_decomposability_matrix

set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {m n : ℕ} (w : Fin n → ℝ) (hw : ∀ k, 0 ≤ w k)
    (y p : Fin n → Fin m → ℝ) (hy : ∀ k a, 0 ≤ y k a) (hp : ∀ k a, 0 ≤ p k a)
    (a b : Fin 4 → ℝ) (ha : ∀ i, 0 ≤ a i) (hab : ∀ i, a i ≤ b i)
    (hpos : 0 < ∑ j, lin b (classTable (state w y p) j)) :
    measure a b (∑ j, classTable (state w y p) j)
      = ∑ j, (lin b (classTable (state w y p) j) / ∑ l, lin b (classTable (state w y p) l))
          * measure a b (classTable (state w y p) j) :=
  temporal_decomposability_matrix _ (state_nonneg hw hy hp) a b ha hab hpos
end Aggmetrics.DataStream
