-- Prove2me | Definitions.Def_CSL_Circuit_MemoryAccess_PhysicalFramePathData
-- name    : CSL_Circuit_MemoryAccess_PhysicalFramePathData
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:37:11.736895+00:00
-- url     : https://prove2.me/theorems/337e9108-8f8d-4fc4-be16-8d8840fb484c
-- title:
--   Coded sorting library: Circuit / MemoryAccess / PhysicalFramePathData
-- statement:
--   Module `CodedSorting.Circuit.MemoryAccess.PhysicalFramePathData` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Circuit.MemoryAccess.PhysicalFramePathData

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Generated_FiniteCircuit_Data

namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate

/-- The ordinary-frame visit contributed by one literal scalar gate. -/
def ordinaryFrameVisit (r : Nat) (g : Gate) : Option Nat :=
  if g.frame = scatterFrame then none
  else if r ∈ g.destination :: g.sources then some g.frame else none

/-- Chronological gate visits, including repeated visits to the same frame. -/
def ordinaryFrameVisits (r : Nat) (word : List Gate) : List Nat :=
  word.filterMap (ordinaryFrameVisit r)

/-- A small Boolean checker for a literal list of successive frame IDs. -/
def climbPath (start : Nat) : List Nat → Bool
  | [] => true
  | next :: rest => canClimb start next && climbPath next rest

/-- The entire original-register path, including the prescribed terminal. -/
def originalFramePath (r : Nat) : List Nat :=
  ordinaryFrameVisits r gates.toList ++ [finalFrames[r]!]

def originalFramePathValid (r : Nat) : Bool :=
  climbPath startFrames[r]! (originalFramePath r)


end CSL.Construction.PhysicalFramePaths


