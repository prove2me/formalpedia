-- Prove2me | Definitions.Def_r03_defs_308a4c5b4d_v5_FiniteBoundary
-- name    : r03_defs_308a4c5b4d_v5_FiniteBoundary
-- status  : Definition
-- author  : @hao jia
-- created : 2026-09-17T09:52:50.859479+00:00
-- url     : https://prove2.me/theorems/576b3a2b-c3a5-49c7-8dd8-c854e2ea3883
-- title:
--   R03 candidate definition: r03 defs 308a4c5b4d v5 FiniteBoundary
-- statement:
--   This is a source-faithful definition module supporting a conditional formalization of the cubic P3-partition problem. It contains data structures and predicates used by separately published theorem candidates; it does not assert that the open root problem is solved.
-- source:
--   VibeMathing candidate definition artifact: Definitions/Def_r03_defs_308a4c5b4d_v5_FiniteBoundary.lean; candidate-only formalization for ProblemContract problem:opg-46613-p3-partition.

import Mathlib.Data.Fin.VecNotation

/- Candidate finite catalogue; no graph-level semantics or admission. -/
namespace R03FiniteBoundaryV5
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def leafMasks : Fin 16 → Nat := ![0,1,2,3,4,5,6,8,9,10,12,16,17,18,20,24]
def centerMasks : Fin 6 → Nat := ![0,1,2,4,8,16]
def bit (m i : Nat) : Nat := m / 2^i % 2
def ones (m : Nat) : Nat := bit m 0 + bit m 1 + bit m 2 + bit m 3 + bit m 4
def x (a b : Fin 16) (c : Fin 6) (i : Nat) : Nat :=
  bit (if i % 3 = 0 then leafMasks a else if i % 3 = 1 then centerMasks c else leafMasks b) (i / 3)
def d1 (a b : Fin 16) (c : Fin 6) : Nat := x a b c 0 + x a b c 1 + x a b c 2
def d2 (a b : Fin 16) (c : Fin 6) : Nat := x a b c 3 + x a b c 4 + x a b c 5
def d3 (a b : Fin 16) (c : Fin 6) : Nat := x a b c 6 + x a b c 7 + x a b c 8
def d6 (a b : Fin 16) (c : Fin 6) : Nat := x a b c 0 + x a b c 3 + x a b c 6 + x a b c 9 + x a b c 12
def d7 (a b : Fin 16) (c : Fin 6) : Nat := x a b c 1 + x a b c 4 + x a b c 7 + x a b c 10 + x a b c 13
def d8 (a b : Fin 16) (c : Fin 6) : Nat := x a b c 2 + x a b c 5 + x a b c 8 + x a b c 11 + x a b c 14
def total (a b : Fin 16) (c : Fin 6) : Nat := x a b c 0 + x a b c 1 + x a b c 2 + x a b c 3 + x a b c 4 + x a b c 5 + x a b c 6 + x a b c 7 + x a b c 8 + x a b c 9 + x a b c 10 + x a b c 11 + x a b c 12 + x a b c 13 + x a b c 14
def Valid (a b : Fin 16) (c : Fin 6) : Prop :=
  (x a b c 0 + x a b c 1 + x a b c 2) ≤ 1 ∧
  (x a b c 3 + x a b c 4 + x a b c 5) ≤ 1 ∧
  (x a b c 6 + x a b c 7 + x a b c 8) ≤ 2 ∧
  (x a b c 9 + x a b c 10 + x a b c 11) ≤ 2 ∧
  (x a b c 12 + x a b c 13 + x a b c 14) ≤ 2 ∧
  x a b c 0 + x a b c 7 ≤ 1 ∧
  x a b c 0 + x a b c 8 ≤ 1 ∧
  x a b c 0 + x a b c 13 ≤ 1 ∧
  x a b c 0 + x a b c 14 ≤ 1 ∧
  x a b c 2 + x a b c 6 ≤ 1 ∧
  x a b c 2 + x a b c 7 ≤ 1 ∧
  x a b c 2 + x a b c 12 ≤ 1 ∧
  x a b c 2 + x a b c 13 ≤ 1 ∧
  x a b c 3 + x a b c 7 ≤ 1 ∧
  x a b c 3 + x a b c 8 ≤ 1 ∧
  x a b c 3 + x a b c 10 ≤ 1 ∧
  x a b c 3 + x a b c 11 ≤ 1 ∧
  x a b c 5 + x a b c 6 ≤ 1 ∧
  x a b c 5 + x a b c 7 ≤ 1 ∧
  x a b c 5 + x a b c 9 ≤ 1 ∧
  x a b c 5 + x a b c 10 ≤ 1 ∧
  x a b c 6 + x a b c 11 ≤ 1 ∧
  x a b c 6 + x a b c 14 ≤ 1 ∧
  x a b c 7 + x a b c 9 ≤ 1 ∧
  x a b c 7 + x a b c 11 ≤ 1 ∧
  x a b c 7 + x a b c 12 ≤ 1 ∧
  x a b c 7 + x a b c 14 ≤ 1 ∧
  x a b c 8 + x a b c 9 ≤ 1 ∧
  x a b c 8 + x a b c 12 ≤ 1 ∧
  x a b c 9 + x a b c 13 ≤ 1 ∧
  x a b c 9 + x a b c 14 ≤ 1 ∧
  x a b c 10 + x a b c 12 ≤ 1 ∧
  x a b c 10 + x a b c 14 ≤ 1 ∧
  x a b c 11 + x a b c 12 ≤ 1 ∧
  x a b c 11 + x a b c 13 ≤ 1

end R03FiniteBoundaryV5


