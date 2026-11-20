-- Prove2me | solution 1 for Aggmetrics.DataStream.perClass_default
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:18:21.877391+00:00
-- url     : https://prove2.me/submissions/dbe39f59-6c7a-4a85-a1cc-0efab3235c7a

import Definitions.Def_Aggmetrics_DataStreamTemporal
import Definitions.Def_Aggmetrics_DataStreamDelay

set_option autoImplicit true
open Finset Matrix MeasureTheory
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {m : ℕ} (u : Fin m → Bool) (v : Fin m → ℝ) (j : Fin m) :
    (perClass "zero" u v j).isSome ∧ (perClass "one" u v j).isSome := by
  unfold perClass
  by_cases hj : u j = true <;> simp [hj]
end Aggmetrics.DataStream
