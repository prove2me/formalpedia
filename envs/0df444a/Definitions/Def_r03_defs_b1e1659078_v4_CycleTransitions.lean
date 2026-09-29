-- Prove2me | Definitions.Def_r03_defs_b1e1659078_v4_CycleTransitions
-- name    : r03_defs_b1e1659078_v4_CycleTransitions
-- status  : Definition
-- author  : @hao jia
-- created : 2026-09-17T09:53:01.627955+00:00
-- url     : https://prove2.me/theorems/2ea75ce4-c3ea-4f87-8bc7-f39fb70514f3
-- title:
--   R03 candidate definition: r03 defs b1e1659078 v4 CycleTransitions
-- statement:
--   This is a source-faithful definition module supporting a conditional formalization of the cubic P3-partition problem. It contains data structures and predicates used by separately published theorem candidates; it does not assert that the open root problem is solved.
-- source:
--   VibeMathing candidate definition artifact: Definitions/Def_r03_defs_b1e1659078_v4_CycleTransitions.lean; candidate-only formalization for ProblemContract problem:opg-46613-p3-partition.

import Mathlib.Data.Fin.VecNotation

/- Candidate-only local transition certificates. Codes are 0 unused,
   1 incoming, 2 outgoing; a cycle adds t on its entering half-edge and
   -t = 2*t on its leaving half-edge. Global graph faithfulness is separate.
   Degree-count definitions reuse the frozen v3_ChargePatterns candidate. -/
namespace R03CycleCandidateV4
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def ins (a b c : Fin 3) : Nat :=
  (if a = 1 then 1 else 0) + (if b = 1 then 1 else 0) + (if c = 1 then 1 else 0)
def outs (a b c : Fin 3) : Nat :=
  (if a = 2 then 1 else 0) + (if b = 2 then 1 else 0) + (if c = 2 then 1 else 0)
def bad (a b c : Fin 3) : Nat :=
  if ins a b c = 1 ∧ outs a b c = 2 then 1 else 0

end R03CycleCandidateV4


