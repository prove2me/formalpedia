-- Prove2me | Definitions.Def_Aggmetrics_DataStreamDrift
-- name    : Aggmetrics_DataStreamDrift
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T10:28:57.047309+00:00
-- url     : https://prove2.me/theorems/17479d6f-70c6-4036-b987-22dc21ae9ed3
-- title:
--   Data Stream Drift
-- statement:
--   Definitions and structural lemmas for Data Stream Drift, from Ronaldo C. Prati and the Aggmetrics contributors's pinned Aggmetrics: data-stream metric aggregation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDrift.lean

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory Filter
namespace Aggmetrics.DataStream
noncomputable def precision (R S π : ℝ) : ℝ := π * R / (π * R + (1 - π) * (1 - S))
noncomputable def f1 (R S π : ℝ) : ℝ := 2 * π * R / (π * (1 + R) + (1 - π) * (1 - S))
def accuracy (R S π : ℝ) : ℝ := π * R + (1 - π) * S
end Aggmetrics.DataStream


