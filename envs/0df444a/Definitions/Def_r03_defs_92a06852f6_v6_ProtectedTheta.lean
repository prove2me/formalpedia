-- Prove2me | Definitions.Def_r03_defs_92a06852f6_v6_ProtectedTheta
-- name    : r03_defs_92a06852f6_v6_ProtectedTheta
-- status  : Definition
-- author  : @hao jia
-- created : 2026-09-17T01:20:29.704286+00:00
-- url     : https://prove2.me/theorems/c0a1e1bc-8468-4211-aa3f-a2cf08540bef
-- title:
--   R03 P3-factor definition module: r03_defs_92a06852f6_v6_ProtectedTheta
-- statement:
--   This module packages source-faithful finite-graph, matching, port, or bookkeeping structures used by reusable auxiliary theorems in the cubic P3-partition formalization. It contains definitions and structural interfaces only; it does not assert closure of the open root problem.
--
--   **Formalization Note** The code was extracted from the cited candidate artifact and its exact digest is recorded in the campaign ledger.
-- source:
--   VibeMathing candidate artifact: research/artifacts/candidates/r03/v6_ProtectedTheta.lean; source SHA-256 9a5f89a023459e0ec3056acfce8208a237ead9b6fb5790cbd3a5261d6f71635f; ProblemContract problem:opg-46613-p3-partition; candidate-only formalization.

import Mathlib.Data.Fin.VecNotation

/- Candidate-only half-edge calculations, not a graph-level root theorem.
   Codes: 0 unused, 1 incoming, 2 outgoing. A directed cycle adds 1 at
   the entering half-edge and 2 at the leaving one. A theta adds the
   same nonzero code on all three half-edges at either branch. -/
namespace R03ProtectedThetaV6
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def ins (a b c : Fin 3) : Nat :=
  (if a = 1 then 1 else 0) + (if b = 1 then 1 else 0) + (if c = 1 then 1 else 0)
def outs (a b c : Fin 3) : Nat :=
  (if a = 2 then 1 else 0) + (if b = 2 then 1 else 0) + (if c = 2 then 1 else 0)
def bad (a b c : Fin 3) : Nat :=
  if ins a b c = 1 ∧ outs a b c = 2 then 1 else 0

end R03ProtectedThetaV6


