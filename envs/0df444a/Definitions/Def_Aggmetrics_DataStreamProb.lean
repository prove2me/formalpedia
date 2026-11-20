-- Prove2me | Definitions.Def_Aggmetrics_DataStreamProb
-- name    : Aggmetrics_DataStreamProb
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T10:27:54.793234+00:00
-- url     : https://prove2.me/theorems/6c70f6a2-c6fe-43eb-8e53-02ff7771ddbb
-- title:
--   Data Stream Prob
-- statement:
--   Definitions and structural lemmas for Data Stream Prob, from Ronaldo C. Prati and the Aggmetrics contributors's pinned Aggmetrics: data-stream metric aggregation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamProb.lean

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory
namespace Aggmetrics.DataStream
noncomputable def specJoint {m : ℕ} (π : Fin m → ℝ) (c : Fin m → Fin m → ℝ) (j : Fin m) : ℝ :=
  (∑ k ∈ univ.erase j, ∑ l ∈ univ.erase j, π k * c k l) / (∑ k ∈ univ.erase j, π k)
noncomputable def specFormula {m : ℕ} (π : Fin m → ℝ) (c : Fin m → Fin m → ℝ) (j : Fin m) : ℝ :=
  ∑ k ∈ univ.erase j, (π k / (1 - π j)) * (1 - c k j)
end Aggmetrics.DataStream


