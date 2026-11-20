-- Prove2me | solution 1 for Aggmetrics.DataStream.perClass_audit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:18:07.001423+00:00
-- url     : https://prove2.me/submissions/9286929f-2424-42af-a1d1-2413712f2e95

import Definitions.Def_Aggmetrics_DataStreamTemporal
import Definitions.Def_Aggmetrics_DataStreamDelay

set_option autoImplicit true
open Finset Matrix MeasureTheory
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {m : ℕ} (u : Fin m → Bool) (v : Fin m → ℝ) (j : Fin m)
    (hj : u j = false) :
    perClass "exclude" u v j = none ∧ perClass "nan" u v j = none := by
  simp [perClass, hj]
end Aggmetrics.DataStream
