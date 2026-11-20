-- Prove2me | solution 1 for Aggmetrics.DataStream.classTable_state
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:03:23.084276+00:00
-- url     : https://prove2.me/submissions/94d22c13-41aa-49ba-a03d-12107dcd5846

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal
import Theorems.Thm_Aggmetrics_DataStream_classTable_sum

set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {m n : ℕ} (w : Fin n → ℝ) (y p : Fin n → Fin m → ℝ) (j : Fin m) :
    classTable (state w y p) j = ∑ k, w k • classTable (outer (y k) (p k)) j :=
  classTable_sum w (fun k => outer (y k) (p k)) j
end Aggmetrics.DataStream
