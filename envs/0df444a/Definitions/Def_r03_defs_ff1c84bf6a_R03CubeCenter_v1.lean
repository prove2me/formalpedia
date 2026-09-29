-- Prove2me | Definitions.Def_r03_defs_ff1c84bf6a_R03CubeCenter_v1
-- name    : r03_defs_ff1c84bf6a_R03CubeCenter_v1
-- status  : Definition
-- author  : @hao jia
-- created : 2026-09-17T09:53:49.070209+00:00
-- url     : https://prove2.me/theorems/e93cd573-32a8-465e-81e3-37c1a2b8e7f5
-- title:
--   R03 candidate definition: r03 defs ff1c84bf6a R03CubeCenter v1
-- statement:
--   This is a source-faithful definition module supporting a conditional formalization of the cubic P3-partition problem. It contains data structures and predicates used by separately published theorem candidates; it does not assert that the open root problem is solved.
-- source:
--   VibeMathing candidate definition artifact: Definitions/Def_r03_defs_ff1c84bf6a_R03CubeCenter_v1.lean; candidate-only formalization for ProblemContract problem:opg-46613-p3-partition.

import Mathlib.Data.Fin.VecNotation

/- Candidate-only finite cube-center obstruction and scalar bookkeeping.
   The arbitrary-graph factor projector and cycle/fiber identity are not
   formalized in this source. -/
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option synthInstance.maxSize 100000
namespace R03CubeCenter

def chosen (m : Fin 128) (v : Fin 7) : Bool := m.val.testBit v.val

def bit (m : Fin 128) (v : Fin 7) : Nat := if chosen m v then 1 else 0

def cardinality (m : Fin 128) : Nat :=
  bit m 0 + bit m 1 + bit m 2 + bit m 3 + bit m 4 + bit m 5 + bit m 6

def portCount (m : Fin 128) : Nat := bit m 0 + bit m 1 + bit m 3

def adjacent (u v : Fin 7) : Bool :=
  let d := Nat.xor (u.val+1) (v.val+1)
  d==1 || d==2 || d==4

def Dominating (m : Fin 128) : Prop :=
  ∀ v : Fin 7, chosen m v=false →
    ∃ u : Fin 7, chosen m u=true ∧ adjacent u v=true

def HasCenterEdge (m : Fin 128) : Prop :=
  ∃ u v : Fin 7, chosen m u=true ∧ chosen m v=true ∧ adjacent u v=true

end R03CubeCenter


