-- Prove2me | Definitions.Def_ULHC_Phase2
-- name    : ULHC_Phase2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T02:21:47.604799+00:00
-- url     : https://prove2.me/theorems/ef961a82-f5ca-4d1e-a1aa-0d3f9444af3b
-- title:
--   Phase2
-- statement:
--   Definitions and structural lemmas for Phase2, from zzyzek/SolidGridGraphHamiltonianCycle2D-Lean contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Umans-Lenhart Hamiltonian-cycle algorithm for solid grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Phase2.lean

import Definitions.Def_ULHC_Phase
set_option autoImplicit true
namespace ULHC
open Finset Classical
def ParOK (c : Pt) (s : Side) (o : Bool) : Prop := par c = if s.horiz then !o else o
section arcs
variable {F : Finset Edge} {c : Pt} {s : Side} {o : Bool}
end arcs
section phase2
variable {V : Finset Pt} {F H : Finset Edge} {P : Finset Pt}
  (hF : Deg2 V F) (hH : Deg2 V H) (hs : Solid V) (hB : Border V F P)
end phase2
end ULHC


