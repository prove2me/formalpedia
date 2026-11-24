-- Prove2me | Definitions.Def_CSL_Circuit_MemoryAccess_PhysicalFrameWordData
-- name    : CSL_Circuit_MemoryAccess_PhysicalFrameWordData
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:52:10.632188+00:00
-- url     : https://prove2.me/theorems/802d822a-99d6-4c13-9ea0-94a6cb025b7a
-- title:
--   Coded sorting library: Circuit / MemoryAccess / PhysicalFrameWordData
-- statement:
--   Module `CodedSorting.Circuit.MemoryAccess.PhysicalFrameWordData` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Exact numerical port/frame annotations for the physical local words.
--   There are 661 original registers and nine copied temporaries. The fixed
--   copy frames 510,...,518 are checked in the same original-register paths as
--   all other visits; their ranks are separate concrete checks.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Circuit.MemoryAccess.PhysicalFrameWordData

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Circuit_MemoryAccess_PhysicalFramePathData

/-! Exact numerical port/frame annotations for the physical local words.
There are 661 original registers and nine copied temporaries. The fixed
copy frames 510,...,518 are checked in the same original-register paths as
all other visits; their ranks are separate concrete checks.
-/

namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate

structure FrameEvent where
  frame : Nat
  ports : List Nat
  deriving DecidableEq, Repr, Inhabited

def ordinaryEvent (g : Gate) : FrameEvent := ⟨g.frame, g.destination :: g.sources⟩

def copyEvent (t : Nat) : FrameEvent := ⟨510 + t, [472 + t, 661 + t]⟩

def scatterEvent (g : Gate) : FrameEvent :=
  ⟨0, g.destination :: ((List.range 9).filter
    (fun t => (472 + t) ∈ g.sources)).map (fun t => 661 + t)⟩

def eventVisits (r : Nat) (events : List FrameEvent) : List Nat :=
  events.filterMap (fun e => if r ∈ e.ports then some e.frame else none)

def physicalPrefix : List Gate := gates.toList.take beforeScatterCount
def physicalScatter : List Gate := (gates.toList.drop beforeScatterCount).take portCount
def physicalSuffix : List Gate := gates.toList.drop (beforeScatterCount + portCount)

def forwardEvents : List FrameEvent :=
  physicalPrefix.map ordinaryEvent ++ (List.range 9).map copyEvent ++
    physicalScatter.map scatterEvent ++ physicalSuffix.map ordinaryEvent

/-- Frame IDs before taking orthogonal complements. Fresh copies follow the
reversed suffix; no overwrite-copy gate is reversed or treated as invertible. -/
def middleEvents : List FrameEvent :=
  physicalSuffix.reverse.map ordinaryEvent ++ (List.range 9).map copyEvent ++
    physicalScatter.reverse.map scatterEvent ++ physicalPrefix.reverse.map ordinaryEvent

def forwardPathValid (r : Nat) : Bool :=
  climbPath startFrames[r]! (eventVisits r forwardEvents ++ [finalFrames[r]!])

/-- Reversing these IDs permits the same increasing-frame checker. Its
matrix interpretation reverses again and takes the orthogonal complement. -/
def middlePathValid (r : Nat) : Bool :=
  climbPath startFrames[r]! ((eventVisits r middleEvents).reverse ++ [finalFrames[r]!])

def copyFramesValid : Bool :=
  (List.range 9).all (fun t => projections[510+t]!.dimension == 7)

end CSL.Construction.PhysicalFramePaths


