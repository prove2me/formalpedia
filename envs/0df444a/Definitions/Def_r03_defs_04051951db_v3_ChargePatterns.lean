-- Prove2me | Definitions.Def_r03_defs_04051951db_v3_ChargePatterns
-- name    : r03_defs_04051951db_v3_ChargePatterns
-- status  : Definition
-- author  : @hao jia
-- created : 2026-09-17T09:52:49.053576+00:00
-- url     : https://prove2.me/theorems/edf5001f-d280-4354-baad-f63fd129d39c
-- title:
--   R03 candidate definition: r03 defs 04051951db v3 ChargePatterns
-- statement:
--   This is a source-faithful definition module supporting a conditional formalization of the cubic P3-partition problem. It contains data structures and predicates used by separately published theorem candidates; it does not assert that the open root problem is solved.
-- source:
--   VibeMathing candidate definition artifact: Definitions/Def_r03_defs_04051951db_v3_ChargePatterns.lean; candidate-only formalization for ProblemContract problem:opg-46613-p3-partition.

import Mathlib.Data.Fin.VecNotation

/- Local arithmetic candidates for a cubic vertex, not a graph-level proof.
   Fin 3 codes: 0 unused, 1 incoming, 2 outgoing. -/
namespace R03ChargeCandidateV3
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def ins (a b c : Fin 3) : Nat :=
  (if a = 1 then 1 else 0) + (if b = 1 then 1 else 0) + (if c = 1 then 1 else 0)

def outs (a b c : Fin 3) : Nat :=
  (if a = 2 then 1 else 0) + (if b = 2 then 1 else 0) + (if c = 2 then 1 else 0)

def isCenter (a b c : Fin 3) : Nat := if ins a b c = 2 then 1 else 0

def isBad (a b c : Fin 3) : Nat :=
  if ins a b c = 1 ∧ outs a b c = 2 then 1 else 0

end R03ChargeCandidateV3


