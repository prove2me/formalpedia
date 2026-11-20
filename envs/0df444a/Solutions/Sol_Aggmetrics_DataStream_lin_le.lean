-- Prove2me | solution 1 for Aggmetrics.DataStream.lin_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:00:06.095374+00:00
-- url     : https://prove2.me/submissions/553fe4b4-947d-421f-8527-a7fe6c23441c

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal

set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {a b : Fin 4 → ℝ} (hab : ∀ i, a i ≤ b i) {T : Matrix (Fin 2) (Fin 2) ℝ}
    (hT : ∀ r s, 0 ≤ T r s) : lin a T ≤ lin b T := by
  unfold lin
  have h0 := mul_le_mul_of_nonneg_right (hab 0) (hT 0 0)
  have h1 := mul_le_mul_of_nonneg_right (hab 1) (hT 0 1)
  have h2 := mul_le_mul_of_nonneg_right (hab 2) (hT 1 0)
  have h3 := mul_le_mul_of_nonneg_right (hab 3) (hT 1 1)
  linarith
end Aggmetrics.DataStream
