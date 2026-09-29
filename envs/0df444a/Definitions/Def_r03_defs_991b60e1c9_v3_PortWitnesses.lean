-- Prove2me | Definitions.Def_r03_defs_991b60e1c9_v3_PortWitnesses
-- name    : r03_defs_991b60e1c9_v3_PortWitnesses
-- status  : Definition
-- author  : @hao jia
-- created : 2026-09-17T01:20:31.103056+00:00
-- url     : https://prove2.me/theorems/d36117fb-c54c-4775-9716-8c82efa6ee4d
-- title:
--   R03 P3-factor definition module: r03_defs_991b60e1c9_v3_PortWitnesses
-- statement:
--   This module packages source-faithful finite-graph, matching, port, or bookkeeping structures used by reusable auxiliary theorems in the cubic P3-partition formalization. It contains definitions and structural interfaces only; it does not assert closure of the open root problem.
--
--   **Formalization Note** The code was extracted from the cited candidate artifact and its exact digest is recorded in the campaign ledger.
-- source:
--   VibeMathing candidate artifact: research/artifacts/candidates/r03/v3_PortWitnesses.lean; source SHA-256 0da21f63d9055bfb6d45391c7261e5884a4524f79879d83d6f1b27c3eafa9eec; ProblemContract problem:opg-46613-p3-partition; candidate-only formalization.

import Mathlib.Data.Fin.VecNotation

/- Candidate-only local certificates. These declarations do NOT assert
   the frozen root theorem, a graph connectivity theorem, or Result admission.
   0=unused; 1=outside leaf -> inside center; 2=inside leaf -> outside center. -/
namespace R03PortCandidateV3

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def edges : List (Fin 9 × Fin 9) :=
  [(0,1),(0,5),(1,2),(1,6),(2,3),(2,7),
   (3,8),(4,6),(4,7),(5,7),(5,8),(6,8)]

def signatures : Fin 9 → Fin 3 → Fin 3 :=
  ![![2,2,2], ![2,0,1], ![2,1,0], ![0,2,1], ![0,0,0],
    ![0,1,2], ![1,2,0], ![1,0,2], ![1,1,1]]

def witnessArcs : Fin 9 → List (Fin 9 × Fin 9) :=
  ![[(2,1),(6,1),(7,5),(8,5)],
    [(1,2),(3,2),(6,4),(8,5),(7,5)],
    [(1,6),(2,3),(4,6),(7,5),(8,5)],
    [(2,1),(8,5),(0,1),(6,4),(7,5)],
    [(1,0),(2,3),(5,0),(6,4),(7,4),(8,3)],
    [(6,1),(7,5),(0,1),(2,3),(8,5)],
    [(4,6),(5,0),(7,2),(8,6),(1,2)],
    [(3,2),(5,0),(7,2),(8,6),(1,6)],
    [(5,0),(7,4),(8,3),(2,1),(6,1)]]

def boundary (b : Fin 3 → Fin 3) : List (Fin 9 × Fin 3) :=
  [(0,b 0),(3,b 1),(4,b 2)]

def incoming (b : Fin 3 → Fin 3) (arcs : List (Fin 9 × Fin 9)) (v : Fin 9) : Nat :=
  (arcs.filter (fun e => e.2 == v)).length +
  ((boundary b).filter (fun e => e.1 == v && e.2 == 1)).length

def outgoing (b : Fin 3 → Fin 3) (arcs : List (Fin 9 × Fin 9)) (v : Fin 9) : Nat :=
  (arcs.filter (fun e => e.1 == v)).length +
  ((boundary b).filter (fun e => e.1 == v && e.2 == 2)).length

def Valid (b : Fin 3 → Fin 3) (arcs : List (Fin 9 × Fin 9)) : Prop :=
  arcs.Nodup ∧ (∀ e ∈ arcs, e ∈ edges ∨ (e.2,e.1) ∈ edges) ∧
  ∀ v : Fin 9,
    (incoming b arcs v = 2 ∧ outgoing b arcs v = 0) ∨
    (incoming b arcs v = 0 ∧ outgoing b arcs v = 1)

end R03PortCandidateV3


