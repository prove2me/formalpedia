-- Prove2me | Definitions.Def_r03_defs_bbf930aa73_R03PrismPole_v1
-- name    : r03_defs_bbf930aa73_R03PrismPole_v1
-- status  : Definition
-- author  : @hao jia
-- created : 2026-09-17T01:20:06.32912+00:00
-- url     : https://prove2.me/theorems/ef582ca7-838c-49f1-847a-320d97a89b80
-- title:
--   R03 P3-factor definition module: r03_defs_bbf930aa73_R03PrismPole_v1
-- statement:
--   This module packages source-faithful finite-graph, matching, port, or bookkeeping structures used by reusable auxiliary theorems in the cubic P3-partition formalization. It contains definitions and structural interfaces only; it does not assert closure of the open root problem.
--
--   **Formalization Note** The code was extracted from the cited candidate artifact and its exact digest is recorded in the campaign ledger.
-- source:
--   VibeMathing candidate artifact: research/artifacts/candidates/r03/R03PrismPole_v1.lean; source SHA-256 24b405894c7d1726cb7aef6741d97c52ffad611b273b767a5c5ce69d48b809d7; ProblemContract problem:opg-46613-p3-partition; candidate-only formalization.

import Mathlib.Data.Fin.VecNotation

/- Candidate-only certificate for the fixed five-node interface.
   Internal directed edges are 01,02,03,12,14,34 (smaller to larger).
   Boundary half-values are at vertices 2,3,4, respectively.
   Specials 0,1,3 forbid outgoing pairs with middle port unused.
   This file does NOT prove the arbitrary-graph substitution/projection theorem
   and does NOT prove the frozen root's existence assertion. -/
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option synthInstance.maxSize 100000

namespace R03PrismPole

def Unit (a b c : Fin 3) : Prop :=
  a+b+c=2 ∧ (a=0 ∨ b=0 ∨ c=0)

def Special (a b c : Fin 3) : Prop :=
  a+b+c=1 ∧ ¬(a=2 ∧ b=0 ∧ c=2)

def Admissible (x01 x02 x03 x12 x14 x34 h2 h3 h4 : Fin 3) : Prop :=
  Special (2*x01) (2*x02) (2*x03) ∧
  Special x01 (2*x12) (2*x14) ∧
  Unit x02 x12 h2 ∧
  Special x03 (2*x34) h3 ∧
  Unit x14 x34 h4

def contribution (a : Fin 3) : Int :=
  if a=1 then 1 else if a=2 then -1 else 0

def BoundaryNet (a b c : Fin 3) : Int :=
  contribution a + contribution b + contribution c

def BoundaryAllowed (a b c : Fin 3) : Prop :=
  (a=0 ∧ b=0 ∧ c=1) ∨ (a=0 ∧ b=1 ∧ c=0) ∨
  (a=1 ∧ b=0 ∧ c=0) ∨ (a=1 ∧ b=1 ∧ c=2) ∨
  (a=1 ∧ b=2 ∧ c=1)

end R03PrismPole


