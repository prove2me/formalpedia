-- Prove2me | Definitions.Def_r03_defs_2a95c85a43_m4_SupportedCycle
-- name    : r03_defs_2a95c85a43_m4_SupportedCycle
-- status  : Definition
-- author  : @hao jia
-- created : 2026-09-17T01:20:08.834085+00:00
-- url     : https://prove2.me/theorems/48c8afdf-88f4-4175-9c61-98671dd2a4ba
-- title:
--   R03 P3-factor definition module: r03_defs_2a95c85a43_m4_SupportedCycle
-- statement:
--   This module packages source-faithful finite-graph, matching, port, or bookkeeping structures used by reusable auxiliary theorems in the cubic P3-partition formalization. It contains definitions and structural interfaces only; it does not assert closure of the open root problem.
--
--   **Formalization Note** The code was extracted from the cited candidate artifact and its exact digest is recorded in the campaign ledger.
-- source:
--   VibeMathing candidate artifact: research/artifacts/candidates/r03/m4_SupportedCycle.lean; source SHA-256 0e8176a98d63eeb2ca57885e32a6fdb569e7a0ff9da73cb1cf61a0ef0a926423; ProblemContract problem:opg-46613-p3-partition; candidate-only formalization.

import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pi

/- Candidate mixed-charge local laws; no graph-level trusted challenge. -/
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
namespace R03MixedChargeM4

abbrev Codes := Fin 3 → Fin 3
def charge (charged : Bool) : Fin 3 := if charged then 2 else 0
def total (a : Codes) : Fin 3 := a 0 + a 1 + a 2
def weight (charged : Bool) (a : Codes) : Nat :=
  if charged then (if a 0 ≠ 0 ∧ a 1 ≠ 0 ∧ a 2 ≠ 0 then 1 else 0)
  else (if a = ![1,1,1] then 1 else 0)
def portDelta (d : Codes) : Prop := d 0 ≠ d 1 ∧ d 1 ≠ d 2 ∧ d 2 ≠ d 0
instance (d : Codes) : Decidable (portDelta d) := inferInstanceAs
  (Decidable (d 0 ≠ d 1 ∧ d 1 ≠ d 2 ∧ d 2 ≠ d 0))
def supported (a d : Codes) : Prop := ∀ i : Fin 3, d i ≠ 0 → a i ≠ 0
instance (a d : Codes) : Decidable (supported a d) := inferInstanceAs
  (Decidable (∀ i : Fin 3, d i ≠ 0 → a i ≠ 0))

end R03MixedChargeM4


