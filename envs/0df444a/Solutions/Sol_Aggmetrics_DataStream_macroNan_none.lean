-- Prove2me | solution 1 for Aggmetrics.DataStream.macroNan_none
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:17:46.339628+00:00
-- url     : https://prove2.me/submissions/5a037816-d9f4-4cae-8262-3c7f6f6e7739

import Definitions.Def_Aggmetrics_DataStreamTemporal
import Definitions.Def_Aggmetrics_DataStreamDelay

set_option autoImplicit true
open Finset Matrix MeasureTheory
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {m : ℕ} (u : Fin m → Bool) (v : Fin m → ℝ) (h : ∃ j, u j = false) :
    macroNan u v = none := by
  obtain ⟨j, hj⟩ := h
  unfold macroNan
  rw [if_neg]
  intro hall
  have := hall j
  simp [hj] at this
end Aggmetrics.DataStream
