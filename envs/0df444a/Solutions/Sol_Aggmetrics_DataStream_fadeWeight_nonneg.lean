-- Prove2me | solution 1 for Aggmetrics.DataStream.fadeWeight_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:04:19.527634+00:00
-- url     : https://prove2.me/submissions/9c9e282f-fdd9-4dfc-bec6-ec3c336a75d5

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal

set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) (n k : ℕ) : 0 ≤ fadeWeight α n k :=
  mul_nonneg (by linarith) (pow_nonneg h0 _)
end Aggmetrics.DataStream
