-- Prove2me | Definitions.Def_Aggmetrics_DataStreamExample
-- name    : Aggmetrics_DataStreamExample
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T09:57:31.891889+00:00
-- url     : https://prove2.me/theorems/6fb83d3e-9037-4754-a3d9-80eee3a3ad7d
-- title:
--   Data Stream Example
-- statement:
--   Definitions and structural lemmas for Data Stream Example, from Ronaldo C. Prati and the Aggmetrics contributors's pinned Aggmetrics: data-stream metric aggregation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamExample.lean

import Definitions.Def_Aggmetrics_DataStreamTemporal
set_option autoImplicit true
open Finset Matrix
namespace Aggmetrics.DataStream.RunningExample
def lab : ℕ → Fin 3
  | 0 => 0 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 1 | 5 => 0 | 6 => 1 | 7 => 1 | _ => 0
def pre : ℕ → Fin 3
  | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 1 | 5 => 0 | 6 => 2 | 7 => 1 | _ => 0
noncomputable def y : ℕ → Fin 3 → ℝ := fun k j => if lab k = j then 1 else 0
noncomputable def p : ℕ → Fin 3 → ℝ := fun k j => if pre k = j then 1 else 0
def aPrec : Fin 4 → ℝ := ![1, 0, 0, 0]
def bPrec : Fin 4 → ℝ := ![1, 0, 1, 0]
end Aggmetrics.DataStream.RunningExample


