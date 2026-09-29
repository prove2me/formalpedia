-- Prove2me | Definitions.Def_r03_defs_8bd867affd_R03PrismPole_v2
-- name    : r03_defs_8bd867affd_R03PrismPole_v2
-- status  : Definition
-- author  : @hao jia
-- created : 2026-09-17T01:20:08.408945+00:00
-- url     : https://prove2.me/theorems/c5e06de8-8eed-42c3-847f-e6bad6f10399
-- title:
--   R03 P3-factor definition module: r03_defs_8bd867affd_R03PrismPole_v2
-- statement:
--   This module packages source-faithful finite-graph, matching, port, or bookkeeping structures used by reusable auxiliary theorems in the cubic P3-partition formalization. It contains definitions and structural interfaces only; it does not assert closure of the open root problem.
--
--   **Formalization Note** The code was extracted from the cited candidate artifact and its exact digest is recorded in the campaign ledger.
-- source:
--   VibeMathing candidate artifact: research/artifacts/candidates/r03/R03PrismPole_v2.lean; source SHA-256 7b4b7091962d85a93933ec5f56e12bd053ac2bd23b6ffa07f33b093c1bc38465; ProblemContract problem:opg-46613-p3-partition; candidate-only formalization.

import Mathlib.Data.Fin.VecNotation

/- Candidate-only local interface and scalar gluing certificate.
   Internal directed edges: 01,02,03,12,14,34 (smaller to larger).
   Boundary half-values: vertices 2,3,4. Specials 0,1,3 exclude outgoing
   pairs with their middle port unused. No arbitrary-graph projector,
   substituted-graph connectivity theorem or root existence is asserted. -/
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


