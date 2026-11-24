-- Prove2me | Definitions.Def_CSL_Generated_MemoryAccess_Group06
-- name    : CSL_Generated_MemoryAccess_Group06
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T13:31:43.014156+00:00
-- url     : https://prove2.me/theorems/2f06924b-056e-4140-b101-b96ed5a007c3
-- title:
--   Coded sorting library: Generated / MemoryAccess / Group06
-- statement:
--   Module `CodedSorting.Generated.MemoryAccess.Group06` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Generated.MemoryAccess.Group06

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Circuit_MemoryAccess_PhysicalFrameEventChunkData
import Definitions.Def_CSL_Generated_MemoryAccess_Base

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 100. -/
def forwardVisitTree100 : VisitTree := (VisitTree.branch 93 (VisitTree.branch 37 (VisitTree.branch 12 (VisitTree.branch 5 (VisitTree.branch 2 (VisitTree.leaf 0 [1]) (VisitTree.leaf 2 [1])) (VisitTree.branch 8 (VisitTree.leaf 5 [1]) (VisitTree.branch 9 (VisitTree.leaf 8 [1, 1]) (VisitTree.leaf 9 [1])))) (VisitTree.branch 25 (VisitTree.branch 21 (VisitTree.leaf 12 [1]) (VisitTree.leaf 21 [1])) (VisitTree.branch 31 (VisitTree.leaf 25 [1]) (VisitTree.branch 34 (VisitTree.leaf 31 [1, 1, 1]) (VisitTree.leaf 34 [1]))))) (VisitTree.branch 62 (VisitTree.branch 40 (VisitTree.branch 39 (VisitTree.leaf 37 [1, 1]) (VisitTree.leaf 39 [1])) (VisitTree.branch 45 (VisitTree.leaf 40 [1, 1, 1, 1, 1, 1, 1]) (VisitTree.branch 48 (VisitTree.leaf 45 [1]) (VisitTree.leaf 48 [1])))) (VisitTree.branch 78 (VisitTree.branch 69 (VisitTree.leaf 62 [1]) (VisitTree.branch 73 (VisitTree.leaf 69 [1]) (VisitTree.leaf 73 [1]))) (VisitTree.branch 81 (VisitTree.leaf 78 [1, 1, 1, 1]) (VisitTree.branch 86 (VisitTree.leaf 81 [1, 1]) (VisitTree.leaf 86 [1, 1])))))) (VisitTree.branch 457 (VisitTree.branch 235 (VisitTree.branch 105 (VisitTree.branch 99 (VisitTree.leaf 93 [1]) (VisitTree.leaf 99 [1])) (VisitTree.branch 106 (VisitTree.leaf 105 [1]) (VisitTree.branch 110 (VisitTree.leaf 106 [1]) (VisitTree.leaf 110 [1, 1, 1, 1, 1, 1, 1, 1])))) (VisitTree.branch 247 (VisitTree.branch 243 (VisitTree.leaf 235 [1]) (VisitTree.leaf 243 [1])) (VisitTree.branch 272 (VisitTree.leaf 247 [1]) (VisitTree.branch 429 (VisitTree.leaf 272 [1]) (VisitTree.leaf 429 [1]))))) (VisitTree.branch 539 (VisitTree.branch 481 (VisitTree.branch 461 (VisitTree.leaf 457 [1]) (VisitTree.leaf 461 [1])) (VisitTree.branch 485 (VisitTree.leaf 481 [1]) (VisitTree.branch 501 (VisitTree.leaf 485 [1]) (VisitTree.leaf 501 [1])))) (VisitTree.branch 627 (VisitTree.branch 611 (VisitTree.leaf 539 [1]) (VisitTree.branch 618 (VisitTree.leaf 611 [1]) (VisitTree.leaf 618 [1]))) (VisitTree.branch 629 (VisitTree.leaf 627 [1]) (VisitTree.branch 644 (VisitTree.leaf 629 [1]) (VisitTree.leaf 644 [1])))))))

def fastForwardChunkVisits100 (r : Nat) : List Nat :=
  forwardVisitTree100.lookup r

private theorem covered100 :
    visitsCovered forwardEventChunk100 forwardVisitTree100 = true := by
  decide +kernel

private theorem checked100 :
    visitsChecked forwardEventChunk100 forwardVisitTree100 = true := by
  decide +kernel

theorem eventVisits_forwardChunk100 (r : Nat) :
    eventVisits r forwardEventChunk100 = fastForwardChunkVisits100 r :=
  eventVisits_of_tree _ _ covered100 checked100 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk100

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 101. -/
def forwardVisitTree101 : VisitTree := (VisitTree.branch 73 (VisitTree.branch 20 (VisitTree.branch 8 (VisitTree.branch 4 (VisitTree.leaf 2 [1, 1]) (VisitTree.leaf 4 [1, 1])) (VisitTree.branch 12 (VisitTree.leaf 8 [1, 1, 1, 1]) (VisitTree.leaf 12 [1, 1]))) (VisitTree.branch 37 (VisitTree.branch 31 (VisitTree.leaf 20 [1, 1, 1, 1]) (VisitTree.leaf 31 [1, 1, 1, 1, 1, 1])) (VisitTree.branch 40 (VisitTree.leaf 37 [1, 1, 1]) (VisitTree.branch 45 (VisitTree.leaf 40 [1, 1, 1, 1, 1]) (VisitTree.leaf 45 [1]))))) (VisitTree.branch 88 (VisitTree.branch 81 (VisitTree.branch 78 (VisitTree.leaf 73 [1, 1, 1, 1, 1, 1]) (VisitTree.leaf 78 [1, 1])) (VisitTree.branch 86 (VisitTree.leaf 81 [1, 1]) (VisitTree.leaf 86 [1, 1, 1, 1]))) (VisitTree.branch 103 (VisitTree.branch 93 (VisitTree.leaf 88 [1, 1, 1]) (VisitTree.leaf 93 [1])) (VisitTree.branch 105 (VisitTree.leaf 103 [1, 1]) (VisitTree.branch 110 (VisitTree.leaf 105 [1, 1, 1, 1, 1, 1]) (VisitTree.leaf 110 [1, 1, 1, 1, 1, 1, 1, 1, 1]))))))

def fastForwardChunkVisits101 (r : Nat) : List Nat :=
  forwardVisitTree101.lookup r

private theorem covered101 :
    visitsCovered forwardEventChunk101 forwardVisitTree101 = true := by
  decide +kernel

private theorem checked101 :
    visitsChecked forwardEventChunk101 forwardVisitTree101 = true := by
  decide +kernel

theorem eventVisits_forwardChunk101 (r : Nat) :
    eventVisits r forwardEventChunk101 = fastForwardChunkVisits101 r :=
  eventVisits_of_tree _ _ covered101 checked101 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk101

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 102. -/
def forwardVisitTree102 : VisitTree := (VisitTree.branch 88 (VisitTree.branch 16 (VisitTree.branch 4 (VisitTree.leaf 2 [1, 1, 1, 1, 1]) (VisitTree.branch 14 (VisitTree.leaf 4 [1]) (VisitTree.leaf 14 [1, 1, 1, 1, 1, 1]))) (VisitTree.branch 18 (VisitTree.leaf 16 [1, 1, 1, 1]) (VisitTree.branch 20 (VisitTree.leaf 18 [1, 1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 20 [1, 1, 1, 1, 1, 1, 1, 1, 1, 1])))) (VisitTree.branch 95 (VisitTree.branch 90 (VisitTree.leaf 88 [1, 1, 1, 1, 1]) (VisitTree.branch 93 (VisitTree.leaf 90 [1, 1, 1]) (VisitTree.leaf 93 [1, 1, 1, 1, 1]))) (VisitTree.branch 103 (VisitTree.leaf 95 [1, 1, 1, 1, 1]) (VisitTree.branch 109 (VisitTree.leaf 103 [1, 1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 109 [1, 1, 1, 1])))))

def fastForwardChunkVisits102 (r : Nat) : List Nat :=
  forwardVisitTree102.lookup r

private theorem covered102 :
    visitsCovered forwardEventChunk102 forwardVisitTree102 = true := by
  decide +kernel

private theorem checked102 :
    visitsChecked forwardEventChunk102 forwardVisitTree102 = true := by
  decide +kernel

theorem eventVisits_forwardChunk102 (r : Nat) :
    eventVisits r forwardEventChunk102 = fastForwardChunkVisits102 r :=
  eventVisits_of_tree _ _ covered102 checked102 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk102

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 103. -/
def forwardVisitTree103 : VisitTree := (VisitTree.branch 88 (VisitTree.branch 16 (VisitTree.branch 4 (VisitTree.branch 2 (VisitTree.leaf 1 [1, 1, 1, 1]) (VisitTree.leaf 2 [1])) (VisitTree.branch 7 (VisitTree.leaf 4 [1]) (VisitTree.leaf 7 [1, 1, 1, 1, 1, 1]))) (VisitTree.branch 25 (VisitTree.branch 24 (VisitTree.leaf 16 [1]) (VisitTree.leaf 24 [1, 1])) (VisitTree.branch 28 (VisitTree.leaf 25 [1, 1, 1]) (VisitTree.branch 29 (VisitTree.leaf 28 [1, 1, 1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 29 [1, 1, 1, 1, 1, 1]))))) (VisitTree.branch 101 (VisitTree.branch 98 (VisitTree.branch 93 (VisitTree.leaf 88 [1]) (VisitTree.leaf 93 [1])) (VisitTree.branch 99 (VisitTree.leaf 98 [1, 1, 1]) (VisitTree.branch 100 (VisitTree.leaf 99 [1, 1]) (VisitTree.leaf 100 [1, 1])))) (VisitTree.branch 106 (VisitTree.branch 103 (VisitTree.leaf 101 [1, 1, 1, 1]) (VisitTree.leaf 103 [1, 1, 1, 1, 1, 1])) (VisitTree.branch 108 (VisitTree.leaf 106 [1, 1, 1]) (VisitTree.branch 109 (VisitTree.leaf 108 [1, 1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 109 [1]))))))

def fastForwardChunkVisits103 (r : Nat) : List Nat :=
  forwardVisitTree103.lookup r

private theorem covered103 :
    visitsCovered forwardEventChunk103 forwardVisitTree103 = true := by
  decide +kernel

private theorem checked103 :
    visitsChecked forwardEventChunk103 forwardVisitTree103 = true := by
  decide +kernel

theorem eventVisits_forwardChunk103 (r : Nat) :
    eventVisits r forwardEventChunk103 = fastForwardChunkVisits103 r :=
  eventVisits_of_tree _ _ covered103 checked103 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk103

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 104. -/
def forwardVisitTree104 : VisitTree := (VisitTree.branch 76 (VisitTree.branch 25 (VisitTree.branch 10 (VisitTree.branch 7 (VisitTree.leaf 1 [1, 1]) (VisitTree.leaf 7 [1, 1])) (VisitTree.branch 13 (VisitTree.leaf 10 [1, 1, 1, 1]) (VisitTree.branch 24 (VisitTree.leaf 13 [1, 1]) (VisitTree.leaf 24 [1, 1])))) (VisitTree.branch 34 (VisitTree.branch 28 (VisitTree.leaf 25 [1, 1, 1]) (VisitTree.branch 29 (VisitTree.leaf 28 [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 29 [1, 1, 1]))) (VisitTree.branch 39 (VisitTree.leaf 34 [1, 1]) (VisitTree.branch 42 (VisitTree.leaf 39 [1]) (VisitTree.leaf 42 [1, 1]))))) (VisitTree.branch 100 (VisitTree.branch 83 (VisitTree.branch 79 (VisitTree.leaf 76 [1, 1]) (VisitTree.leaf 79 [1, 1])) (VisitTree.branch 98 (VisitTree.leaf 83 [1, 1, 1, 1, 1, 1, 1]) (VisitTree.branch 99 (VisitTree.leaf 98 [1]) (VisitTree.leaf 99 [1, 1])))) (VisitTree.branch 106 (VisitTree.branch 101 (VisitTree.leaf 100 [1, 1]) (VisitTree.branch 104 (VisitTree.leaf 101 [1, 1, 1]) (VisitTree.leaf 104 [1, 1, 1, 1]))) (VisitTree.branch 107 (VisitTree.leaf 106 [1]) (VisitTree.branch 108 (VisitTree.leaf 107 [1, 1, 1, 1]) (VisitTree.leaf 108 [1, 1]))))))

def fastForwardChunkVisits104 (r : Nat) : List Nat :=
  forwardVisitTree104.lookup r

private theorem covered104 :
    visitsCovered forwardEventChunk104 forwardVisitTree104 = true := by
  decide +kernel

private theorem checked104 :
    visitsChecked forwardEventChunk104 forwardVisitTree104 = true := by
  decide +kernel

theorem eventVisits_forwardChunk104 (r : Nat) :
    eventVisits r forwardEventChunk104 = fastForwardChunkVisits104 r :=
  eventVisits_of_tree _ _ covered104 checked104 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk104

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 105. -/
def forwardVisitTree105 : VisitTree := (VisitTree.branch 76 (VisitTree.branch 34 (VisitTree.branch 13 (VisitTree.leaf 10 [1, 1, 1, 1]) (VisitTree.branch 32 (VisitTree.leaf 13 [1, 1, 1, 1, 1]) (VisitTree.leaf 32 [1, 1, 1, 1]))) (VisitTree.branch 39 (VisitTree.leaf 34 [1, 1, 1, 1, 1, 1]) (VisitTree.branch 42 (VisitTree.leaf 39 [1, 1, 1]) (VisitTree.leaf 42 [1, 1, 1, 1, 1])))) (VisitTree.branch 85 (VisitTree.branch 79 (VisitTree.leaf 76 [1, 1, 1, 1]) (VisitTree.branch 83 (VisitTree.leaf 79 [1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 83 [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))) (VisitTree.branch 104 (VisitTree.leaf 85 [1, 1, 1, 1, 1]) (VisitTree.branch 107 (VisitTree.leaf 104 [1, 1, 1, 1]) (VisitTree.leaf 107 [1, 1, 1, 1, 1])))))

def fastForwardChunkVisits105 (r : Nat) : List Nat :=
  forwardVisitTree105.lookup r

private theorem covered105 :
    visitsCovered forwardEventChunk105 forwardVisitTree105 = true := by
  decide +kernel

private theorem checked105 :
    visitsChecked forwardEventChunk105 forwardVisitTree105 = true := by
  decide +kernel

theorem eventVisits_forwardChunk105 (r : Nat) :
    eventVisits r forwardEventChunk105 = fastForwardChunkVisits105 r :=
  eventVisits_of_tree _ _ covered105 checked105 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk105

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 106. -/
def forwardVisitTree106 : VisitTree := (VisitTree.branch 55 (VisitTree.branch 38 (VisitTree.branch 22 (VisitTree.leaf 17 [1, 1, 1, 1, 1, 1, 1]) (VisitTree.branch 33 (VisitTree.leaf 22 [1, 1, 1]) (VisitTree.leaf 33 [1, 1, 1, 1, 1, 1, 1]))) (VisitTree.branch 44 (VisitTree.leaf 38 [1, 1, 1, 1, 1]) (VisitTree.branch 50 (VisitTree.leaf 44 [1]) (VisitTree.leaf 50 [1, 1, 1, 1])))) (VisitTree.branch 77 (VisitTree.branch 60 (VisitTree.leaf 55 [1]) (VisitTree.branch 67 (VisitTree.leaf 60 [1, 1, 1]) (VisitTree.leaf 67 [1, 1, 1, 1]))) (VisitTree.branch 92 (VisitTree.branch 87 (VisitTree.leaf 77 [1, 1, 1, 1]) (VisitTree.leaf 87 [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])) (VisitTree.branch 468 (VisitTree.leaf 92 [1, 1, 1, 1, 1]) (VisitTree.leaf 468 [1, 1, 1, 1])))))

def fastForwardChunkVisits106 (r : Nat) : List Nat :=
  forwardVisitTree106.lookup r

private theorem covered106 :
    visitsCovered forwardEventChunk106 forwardVisitTree106 = true := by
  decide +kernel

private theorem checked106 :
    visitsChecked forwardEventChunk106 forwardVisitTree106 = true := by
  decide +kernel

theorem eventVisits_forwardChunk106 (r : Nat) :
    eventVisits r forwardEventChunk106 = fastForwardChunkVisits106 r :=
  eventVisits_of_tree _ _ covered106 checked106 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk106

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 107. -/
def forwardVisitTree107 : VisitTree := (VisitTree.branch 64 (VisitTree.branch 44 (VisitTree.branch 26 (VisitTree.leaf 21 [1, 1, 1, 1, 1, 1]) (VisitTree.branch 36 (VisitTree.leaf 26 [1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 36 [1, 1, 1, 1, 1]))) (VisitTree.branch 51 (VisitTree.leaf 44 [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (VisitTree.branch 55 (VisitTree.leaf 51 [1, 1, 1, 1]) (VisitTree.leaf 55 [1, 1, 1, 1, 1, 1])))) (VisitTree.branch 84 (VisitTree.branch 71 (VisitTree.leaf 64 [1, 1, 1]) (VisitTree.branch 80 (VisitTree.leaf 71 [1, 1, 1]) (VisitTree.leaf 80 [1, 1, 1, 1, 1]))) (VisitTree.branch 94 (VisitTree.leaf 84 [1, 1, 1]) (VisitTree.branch 102 (VisitTree.leaf 94 [1, 1, 1, 1, 1, 1]) (VisitTree.leaf 102 [1, 1, 1, 1, 1])))))

def fastForwardChunkVisits107 (r : Nat) : List Nat :=
  forwardVisitTree107.lookup r

private theorem covered107 :
    visitsCovered forwardEventChunk107 forwardVisitTree107 = true := by
  decide +kernel

private theorem checked107 :
    visitsChecked forwardEventChunk107 forwardVisitTree107 = true := by
  decide +kernel

theorem eventVisits_forwardChunk107 (r : Nat) :
    eventVisits r forwardEventChunk107 = fastForwardChunkVisits107 r :=
  eventVisits_of_tree _ _ covered107 checked107 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk107

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 108. -/
def forwardVisitTree108 : VisitTree := (VisitTree.branch 64 (VisitTree.branch 43 (VisitTree.branch 35 (VisitTree.branch 27 (VisitTree.leaf 19 [1, 1, 1]) (VisitTree.leaf 27 [1, 1, 1])) (VisitTree.branch 36 (VisitTree.leaf 35 [1, 1, 1, 1, 1]) (VisitTree.leaf 36 [1]))) (VisitTree.branch 51 (VisitTree.branch 44 (VisitTree.leaf 43 [1, 1, 1, 1, 1, 1]) (VisitTree.leaf 44 [1, 1])) (VisitTree.branch 55 (VisitTree.leaf 51 [1]) (VisitTree.branch 57 (VisitTree.leaf 55 [1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 57 [1]))))) (VisitTree.branch 80 (VisitTree.branch 66 (VisitTree.branch 65 (VisitTree.leaf 64 [1]) (VisitTree.leaf 65 [1])) (VisitTree.branch 71 (VisitTree.leaf 66 [1, 1, 1, 1, 1, 1]) (VisitTree.branch 74 (VisitTree.leaf 71 [1]) (VisitTree.leaf 74 [1, 1, 1, 1, 1, 1])))) (VisitTree.branch 89 (VisitTree.branch 84 (VisitTree.leaf 80 [1]) (VisitTree.leaf 84 [1, 1])) (VisitTree.branch 97 (VisitTree.leaf 89 [1, 1, 1, 1, 1, 1]) (VisitTree.branch 466 (VisitTree.leaf 97 [1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 466 [1, 1, 1, 1]))))))

def fastForwardChunkVisits108 (r : Nat) : List Nat :=
  forwardVisitTree108.lookup r

private theorem covered108 :
    visitsCovered forwardEventChunk108 forwardVisitTree108 = true := by
  decide +kernel

private theorem checked108 :
    visitsChecked forwardEventChunk108 forwardVisitTree108 = true := by
  decide +kernel

theorem eventVisits_forwardChunk108 (r : Nat) :
    eventVisits r forwardEventChunk108 = fastForwardChunkVisits108 r :=
  eventVisits_of_tree _ _ covered108 checked108 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk108

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 109. -/
def forwardVisitTree109 : VisitTree := (VisitTree.branch 57 (VisitTree.branch 35 (VisitTree.branch 23 (VisitTree.branch 19 (VisitTree.leaf 15 [1, 1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 19 [1, 1])) (VisitTree.branch 27 (VisitTree.leaf 23 [1, 1, 1]) (VisitTree.branch 30 (VisitTree.leaf 27 [1]) (VisitTree.leaf 30 [1, 1])))) (VisitTree.branch 43 (VisitTree.branch 41 (VisitTree.leaf 35 [1, 1]) (VisitTree.leaf 41 [1, 1])) (VisitTree.branch 49 (VisitTree.leaf 43 [1, 1]) (VisitTree.branch 53 (VisitTree.leaf 49 [1, 1, 1, 1]) (VisitTree.leaf 53 [1, 1, 1, 1]))))) (VisitTree.branch 74 (VisitTree.branch 65 (VisitTree.branch 59 (VisitTree.leaf 57 [1]) (VisitTree.leaf 59 [1, 1, 1, 1, 1, 1, 1, 1])) (VisitTree.branch 66 (VisitTree.leaf 65 [1]) (VisitTree.branch 70 (VisitTree.leaf 66 [1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 70 [1, 1])))) (VisitTree.branch 91 (VisitTree.branch 82 (VisitTree.leaf 74 [1, 1]) (VisitTree.branch 89 (VisitTree.leaf 82 [1, 1]) (VisitTree.leaf 89 [1, 1, 1, 1, 1, 1]))) (VisitTree.branch 96 (VisitTree.leaf 91 [1]) (VisitTree.branch 97 (VisitTree.leaf 96 [1, 1]) (VisitTree.leaf 97 [1, 1]))))))

def fastForwardChunkVisits109 (r : Nat) : List Nat :=
  forwardVisitTree109.lookup r

private theorem covered109 :
    visitsCovered forwardEventChunk109 forwardVisitTree109 = true := by
  decide +kernel

private theorem checked109 :
    visitsChecked forwardEventChunk109 forwardVisitTree109 = true := by
  decide +kernel

theorem eventVisits_forwardChunk109 (r : Nat) :
    eventVisits r forwardEventChunk109 = fastForwardChunkVisits109 r :=
  eventVisits_of_tree _ _ covered109 checked109 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk109

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 110. -/
def forwardVisitTree110 : VisitTree := (VisitTree.branch 63 (VisitTree.branch 30 (VisitTree.branch 15 (VisitTree.branch 11 (VisitTree.leaf 3 [1, 1, 1, 1]) (VisitTree.leaf 11 [1, 1, 1])) (VisitTree.branch 23 (VisitTree.leaf 15 [1, 1, 1, 1]) (VisitTree.leaf 23 [1]))) (VisitTree.branch 49 (VisitTree.branch 41 (VisitTree.leaf 30 [1, 1, 1, 1]) (VisitTree.leaf 41 [1, 1, 1, 1])) (VisitTree.branch 53 (VisitTree.leaf 49 [1, 1, 1]) (VisitTree.branch 59 (VisitTree.leaf 53 [1, 1, 1]) (VisitTree.leaf 59 [1, 1, 1, 1, 1, 1, 1, 1]))))) (VisitTree.branch 75 (VisitTree.branch 69 (VisitTree.branch 68 (VisitTree.leaf 63 [1, 1]) (VisitTree.leaf 68 [1, 1, 1, 1])) (VisitTree.branch 70 (VisitTree.leaf 69 [1, 1, 1]) (VisitTree.leaf 70 [1, 1, 1, 1]))) (VisitTree.branch 91 (VisitTree.branch 82 (VisitTree.leaf 75 [1, 1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 82 [1, 1, 1, 1, 1])) (VisitTree.branch 96 (VisitTree.leaf 91 [1]) (VisitTree.branch 465 (VisitTree.leaf 96 [1]) (VisitTree.leaf 465 [1, 1]))))))

def fastForwardChunkVisits110 (r : Nat) : List Nat :=
  forwardVisitTree110.lookup r

private theorem covered110 :
    visitsCovered forwardEventChunk110 forwardVisitTree110 = true := by
  decide +kernel

private theorem checked110 :
    visitsChecked forwardEventChunk110 forwardVisitTree110 = true := by
  decide +kernel

theorem eventVisits_forwardChunk110 (r : Nat) :
    eventVisits r forwardEventChunk110 = fastForwardChunkVisits110 r :=
  eventVisits_of_tree _ _ covered110 checked110 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk110

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 111. -/
def forwardVisitTree111 : VisitTree := (VisitTree.branch 56 (VisitTree.branch 11 (VisitTree.branch 5 (VisitTree.branch 3 (VisitTree.leaf 0 [1, 1, 1, 1, 1, 1]) (VisitTree.leaf 3 [1, 1, 1, 1])) (VisitTree.branch 9 (VisitTree.leaf 5 [1]) (VisitTree.leaf 9 [1]))) (VisitTree.branch 52 (VisitTree.branch 47 (VisitTree.leaf 11 [1, 1]) (VisitTree.leaf 47 [1])) (VisitTree.branch 54 (VisitTree.leaf 52 [1, 1, 1, 1, 1, 1]) (VisitTree.leaf 54 [1])))) (VisitTree.branch 63 (VisitTree.branch 61 (VisitTree.branch 58 (VisitTree.leaf 56 [1]) (VisitTree.leaf 58 [1])) (VisitTree.branch 62 (VisitTree.leaf 61 [1, 1, 1, 1, 1, 1]) (VisitTree.leaf 62 [1, 1, 1, 1, 1, 1, 1]))) (VisitTree.branch 69 (VisitTree.branch 68 (VisitTree.leaf 63 [1, 1, 1, 1, 1]) (VisitTree.leaf 68 [1, 1, 1, 1, 1, 1, 1, 1])) (VisitTree.branch 72 (VisitTree.leaf 69 [1, 1, 1, 1, 1, 1]) (VisitTree.branch 465 (VisitTree.leaf 72 [1, 1, 1, 1, 1]) (VisitTree.leaf 465 [1, 1, 1]))))))

def fastForwardChunkVisits111 (r : Nat) : List Nat :=
  forwardVisitTree111.lookup r

private theorem covered111 :
    visitsCovered forwardEventChunk111 forwardVisitTree111 = true := by
  decide +kernel

private theorem checked111 :
    visitsChecked forwardEventChunk111 forwardVisitTree111 = true := by
  decide +kernel

theorem eventVisits_forwardChunk111 (r : Nat) :
    eventVisits r forwardEventChunk111 = fastForwardChunkVisits111 r :=
  eventVisits_of_tree _ _ covered111 checked111 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk111

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 112. -/
def forwardVisitTree112 : VisitTree := (VisitTree.branch 340 (VisitTree.branch 56 (VisitTree.branch 47 (VisitTree.branch 9 (VisitTree.branch 6 (VisitTree.leaf 5 [1, 1, 1]) (VisitTree.leaf 6 [1, 1, 1])) (VisitTree.branch 46 (VisitTree.leaf 9 [1, 1, 1]) (VisitTree.leaf 46 [1, 1, 1, 1, 1]))) (VisitTree.branch 52 (VisitTree.branch 48 (VisitTree.leaf 47 [1, 1, 1]) (VisitTree.leaf 48 [1, 1, 1, 1, 1, 1])) (VisitTree.branch 54 (VisitTree.leaf 52 [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 54 [1, 1])))) (VisitTree.branch 280 (VisitTree.branch 233 (VisitTree.branch 58 (VisitTree.leaf 56 [1, 1]) (VisitTree.leaf 58 [1, 1])) (VisitTree.branch 241 (VisitTree.leaf 233 [1]) (VisitTree.leaf 241 [1]))) (VisitTree.branch 328 (VisitTree.branch 296 (VisitTree.leaf 280 [1]) (VisitTree.leaf 296 [1])) (VisitTree.branch 331 (VisitTree.leaf 328 [1]) (VisitTree.branch 337 (VisitTree.leaf 331 [1]) (VisitTree.leaf 337 [1])))))) (VisitTree.branch 476 (VisitTree.branch 387 (VisitTree.branch 368 (VisitTree.branch 341 (VisitTree.leaf 340 [1]) (VisitTree.leaf 341 [1])) (VisitTree.branch 385 (VisitTree.leaf 368 [1]) (VisitTree.leaf 385 [1]))) (VisitTree.branch 444 (VisitTree.branch 413 (VisitTree.leaf 387 [1]) (VisitTree.leaf 413 [1])) (VisitTree.branch 475 (VisitTree.leaf 444 [1]) (VisitTree.leaf 475 [1, 1])))) (VisitTree.branch 480 (VisitTree.branch 478 (VisitTree.branch 477 (VisitTree.leaf 476 [1, 1]) (VisitTree.leaf 477 [1, 1])) (VisitTree.branch 479 (VisitTree.leaf 478 [1, 1]) (VisitTree.leaf 479 [1, 1]))) (VisitTree.branch 495 (VisitTree.branch 487 (VisitTree.leaf 480 [1, 1]) (VisitTree.leaf 487 [1])) (VisitTree.branch 538 (VisitTree.leaf 495 [1]) (VisitTree.branch 561 (VisitTree.leaf 538 [1]) (VisitTree.leaf 561 [1])))))))

def fastForwardChunkVisits112 (r : Nat) : List Nat :=
  forwardVisitTree112.lookup r

private theorem covered112 :
    visitsCovered forwardEventChunk112 forwardVisitTree112 = true := by
  decide +kernel

private theorem checked112 :
    visitsChecked forwardEventChunk112 forwardVisitTree112 = true := by
  decide +kernel

theorem eventVisits_forwardChunk112 (r : Nat) :
    eventVisits r forwardEventChunk112 = fastForwardChunkVisits112 r :=
  eventVisits_of_tree _ _ covered112 checked112 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk112

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 113. -/
def forwardVisitTree113 : VisitTree := (VisitTree.branch 353 (VisitTree.branch 288 (VisitTree.branch 244 (VisitTree.branch 233 (VisitTree.branch 226 (VisitTree.leaf 222 [1]) (VisitTree.branch 229 (VisitTree.leaf 226 [1]) (VisitTree.leaf 229 [1]))) (VisitTree.branch 240 (VisitTree.branch 234 (VisitTree.leaf 233 [1]) (VisitTree.leaf 234 [1])) (VisitTree.branch 241 (VisitTree.leaf 240 [1]) (VisitTree.leaf 241 [1])))) (VisitTree.branch 266 (VisitTree.branch 250 (VisitTree.branch 246 (VisitTree.leaf 244 [1]) (VisitTree.leaf 246 [1])) (VisitTree.branch 252 (VisitTree.leaf 250 [1]) (VisitTree.leaf 252 [1]))) (VisitTree.branch 277 (VisitTree.branch 276 (VisitTree.leaf 266 [1]) (VisitTree.leaf 276 [1])) (VisitTree.branch 287 (VisitTree.leaf 277 [1]) (VisitTree.leaf 287 [1]))))) (VisitTree.branch 328 (VisitTree.branch 305 (VisitTree.branch 296 (VisitTree.branch 294 (VisitTree.leaf 288 [1]) (VisitTree.leaf 294 [1])) (VisitTree.branch 297 (VisitTree.leaf 296 [1]) (VisitTree.leaf 297 [1]))) (VisitTree.branch 319 (VisitTree.branch 316 (VisitTree.leaf 305 [1]) (VisitTree.leaf 316 [1])) (VisitTree.branch 320 (VisitTree.leaf 319 [1]) (VisitTree.leaf 320 [1])))) (VisitTree.branch 343 (VisitTree.branch 337 (VisitTree.branch 332 (VisitTree.leaf 328 [1]) (VisitTree.leaf 332 [1])) (VisitTree.branch 340 (VisitTree.leaf 337 [1]) (VisitTree.leaf 340 [1]))) (VisitTree.branch 349 (VisitTree.branch 344 (VisitTree.leaf 343 [1]) (VisitTree.leaf 344 [1])) (VisitTree.branch 352 (VisitTree.leaf 349 [1]) (VisitTree.leaf 352 [1])))))) (VisitTree.branch 400 (VisitTree.branch 371 (VisitTree.branch 360 (VisitTree.branch 357 (VisitTree.leaf 353 [1]) (VisitTree.branch 358 (VisitTree.leaf 357 [1]) (VisitTree.leaf 358 [1]))) (VisitTree.branch 365 (VisitTree.branch 363 (VisitTree.leaf 360 [1]) (VisitTree.leaf 363 [1])) (VisitTree.branch 369 (VisitTree.leaf 365 [1]) (VisitTree.leaf 369 [1])))) (VisitTree.branch 385 (VisitTree.branch 377 (VisitTree.branch 375 (VisitTree.leaf 371 [1]) (VisitTree.leaf 375 [1])) (VisitTree.branch 381 (VisitTree.leaf 377 [1]) (VisitTree.leaf 381 [1, 1]))) (VisitTree.branch 387 (VisitTree.branch 386 (VisitTree.leaf 385 [1]) (VisitTree.leaf 386 [1])) (VisitTree.branch 394 (VisitTree.leaf 387 [1]) (VisitTree.leaf 394 [1]))))) (VisitTree.branch 448 (VisitTree.branch 428 (VisitTree.branch 409 (VisitTree.branch 407 (VisitTree.leaf 400 [1]) (VisitTree.leaf 407 [1])) (VisitTree.branch 411 (VisitTree.leaf 409 [1]) (VisitTree.leaf 411 [1]))) (VisitTree.branch 443 (VisitTree.branch 430 (VisitTree.leaf 428 [1]) (VisitTree.leaf 430 [1])) (VisitTree.branch 444 (VisitTree.leaf 443 [1]) (VisitTree.leaf 444 [1])))) (VisitTree.branch 474 (VisitTree.branch 472 (VisitTree.branch 452 (VisitTree.leaf 448 [1]) (VisitTree.leaf 452 [1])) (VisitTree.branch 473 (VisitTree.leaf 472 [1, 1]) (VisitTree.leaf 473 [1, 1]))) (VisitTree.branch 509 (VisitTree.branch 486 (VisitTree.leaf 474 [1, 1]) (VisitTree.leaf 486 [1])) (VisitTree.branch 524 (VisitTree.leaf 509 [1, 1]) (VisitTree.leaf 524 [1])))))))

def fastForwardChunkVisits113 (r : Nat) : List Nat :=
  forwardVisitTree113.lookup r

private theorem covered113 :
    visitsCovered forwardEventChunk113 forwardVisitTree113 = true := by
  decide +kernel

private theorem checked113 :
    visitsChecked forwardEventChunk113 forwardVisitTree113 = true := by
  decide +kernel

theorem eventVisits_forwardChunk113 (r : Nat) :
    eventVisits r forwardEventChunk113 = fastForwardChunkVisits113 r :=
  eventVisits_of_tree _ _ covered113 checked113 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk113

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 114. -/
def forwardVisitTree114 : VisitTree := (VisitTree.branch 416 (VisitTree.branch 293 (VisitTree.branch 263 (VisitTree.branch 248 (VisitTree.branch 237 (VisitTree.leaf 227 [1]) (VisitTree.branch 245 (VisitTree.leaf 237 [1]) (VisitTree.leaf 245 [1]))) (VisitTree.branch 257 (VisitTree.branch 254 (VisitTree.leaf 248 [1]) (VisitTree.leaf 254 [1])) (VisitTree.branch 259 (VisitTree.leaf 257 [1]) (VisitTree.leaf 259 [1])))) (VisitTree.branch 278 (VisitTree.branch 271 (VisitTree.branch 267 (VisitTree.leaf 263 [1]) (VisitTree.leaf 267 [1])) (VisitTree.branch 273 (VisitTree.leaf 271 [1]) (VisitTree.leaf 273 [1]))) (VisitTree.branch 284 (VisitTree.branch 283 (VisitTree.leaf 278 [1]) (VisitTree.leaf 283 [1])) (VisitTree.branch 290 (VisitTree.leaf 284 [1]) (VisitTree.leaf 290 [1]))))) (VisitTree.branch 360 (VisitTree.branch 314 (VisitTree.branch 307 (VisitTree.branch 295 (VisitTree.leaf 293 [1]) (VisitTree.leaf 295 [1])) (VisitTree.branch 311 (VisitTree.leaf 307 [1]) (VisitTree.leaf 311 [1]))) (VisitTree.branch 327 (VisitTree.branch 322 (VisitTree.leaf 314 [1]) (VisitTree.leaf 322 [1])) (VisitTree.branch 333 (VisitTree.leaf 327 [1]) (VisitTree.leaf 333 [1])))) (VisitTree.branch 396 (VisitTree.branch 368 (VisitTree.branch 367 (VisitTree.leaf 360 [1]) (VisitTree.leaf 367 [1])) (VisitTree.branch 382 (VisitTree.leaf 368 [1]) (VisitTree.leaf 382 [1]))) (VisitTree.branch 413 (VisitTree.branch 398 (VisitTree.leaf 396 [1]) (VisitTree.leaf 398 [1])) (VisitTree.branch 415 (VisitTree.leaf 413 [1, 1]) (VisitTree.leaf 415 [1])))))) (VisitTree.branch 554 (VisitTree.branch 482 (VisitTree.branch 445 (VisitTree.branch 433 (VisitTree.branch 423 (VisitTree.leaf 416 [1]) (VisitTree.leaf 423 [1])) (VisitTree.branch 435 (VisitTree.leaf 433 [1]) (VisitTree.leaf 435 [1]))) (VisitTree.branch 459 (VisitTree.branch 451 (VisitTree.leaf 445 [1]) (VisitTree.leaf 451 [1])) (VisitTree.branch 469 (VisitTree.leaf 459 [1]) (VisitTree.leaf 469 [1])))) (VisitTree.branch 520 (VisitTree.branch 504 (VisitTree.branch 486 (VisitTree.leaf 482 [1]) (VisitTree.leaf 486 [1])) (VisitTree.branch 519 (VisitTree.leaf 504 [1]) (VisitTree.leaf 519 [1]))) (VisitTree.branch 538 (VisitTree.branch 525 (VisitTree.leaf 520 [1]) (VisitTree.leaf 525 [1])) (VisitTree.branch 542 (VisitTree.leaf 538 [1]) (VisitTree.leaf 542 [1]))))) (VisitTree.branch 608 (VisitTree.branch 574 (VisitTree.branch 562 (VisitTree.branch 557 (VisitTree.leaf 554 [1]) (VisitTree.leaf 557 [1])) (VisitTree.branch 571 (VisitTree.leaf 562 [1]) (VisitTree.leaf 571 [1]))) (VisitTree.branch 603 (VisitTree.branch 595 (VisitTree.leaf 574 [1]) (VisitTree.leaf 595 [1])) (VisitTree.branch 606 (VisitTree.leaf 603 [1]) (VisitTree.leaf 606 [1])))) (VisitTree.branch 646 (VisitTree.branch 639 (VisitTree.branch 619 (VisitTree.leaf 608 [1]) (VisitTree.leaf 619 [1])) (VisitTree.branch 645 (VisitTree.leaf 639 [1]) (VisitTree.leaf 645 [1]))) (VisitTree.branch 659 (VisitTree.branch 651 (VisitTree.leaf 646 [1]) (VisitTree.leaf 651 [1])) (VisitTree.branch 660 (VisitTree.leaf 659 [1]) (VisitTree.leaf 660 [1])))))))

def fastForwardChunkVisits114 (r : Nat) : List Nat :=
  forwardVisitTree114.lookup r

private theorem covered114 :
    visitsCovered forwardEventChunk114 forwardVisitTree114 = true := by
  decide +kernel

private theorem checked114 :
    visitsChecked forwardEventChunk114 forwardVisitTree114 = true := by
  decide +kernel

theorem eventVisits_forwardChunk114 (r : Nat) :
    eventVisits r forwardEventChunk114 = fastForwardChunkVisits114 r :=
  eventVisits_of_tree _ _ covered114 checked114 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk114

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 115. -/
def forwardVisitTree115 : VisitTree := (VisitTree.branch 408 (VisitTree.branch 293 (VisitTree.branch 233 (VisitTree.branch 57 (VisitTree.branch 17 (VisitTree.branch 11 (VisitTree.leaf 6 [1, 1]) (VisitTree.leaf 11 [1])) (VisitTree.branch 43 (VisitTree.leaf 17 [1, 1]) (VisitTree.branch 56 (VisitTree.leaf 43 [1]) (VisitTree.leaf 56 [1, 1])))) (VisitTree.branch 69 (VisitTree.branch 68 (VisitTree.leaf 57 [1]) (VisitTree.leaf 68 [1])) (VisitTree.branch 223 (VisitTree.leaf 69 [1, 1]) (VisitTree.branch 228 (VisitTree.leaf 223 [1]) (VisitTree.leaf 228 [1, 1]))))) (VisitTree.branch 258 (VisitTree.branch 239 (VisitTree.branch 238 (VisitTree.leaf 233 [1, 1, 1]) (VisitTree.leaf 238 [1])) (VisitTree.branch 240 (VisitTree.leaf 239 [1]) (VisitTree.branch 241 (VisitTree.leaf 240 [1]) (VisitTree.leaf 241 [1, 1])))) (VisitTree.branch 282 (VisitTree.branch 271 (VisitTree.leaf 258 [1]) (VisitTree.leaf 271 [1, 1])) (VisitTree.branch 288 (VisitTree.leaf 282 [1]) (VisitTree.branch 289 (VisitTree.leaf 288 [1]) (VisitTree.leaf 289 [1])))))) (VisitTree.branch 357 (VisitTree.branch 319 (VisitTree.branch 301 (VisitTree.branch 297 (VisitTree.leaf 293 [1, 1]) (VisitTree.leaf 297 [1])) (VisitTree.branch 316 (VisitTree.leaf 301 [1]) (VisitTree.branch 317 (VisitTree.leaf 316 [1]) (VisitTree.leaf 317 [1])))) (VisitTree.branch 340 (VisitTree.branch 322 (VisitTree.leaf 319 [1, 1, 1]) (VisitTree.leaf 322 [1, 1])) (VisitTree.branch 349 (VisitTree.leaf 340 [1, 1]) (VisitTree.branch 352 (VisitTree.leaf 349 [1, 1, 1]) (VisitTree.leaf 352 [1, 1]))))) (VisitTree.branch 371 (VisitTree.branch 360 (VisitTree.branch 358 (VisitTree.leaf 357 [1]) (VisitTree.leaf 358 [1, 1])) (VisitTree.branch 365 (VisitTree.leaf 360 [1, 1]) (VisitTree.branch 368 (VisitTree.leaf 365 [1]) (VisitTree.leaf 368 [1])))) (VisitTree.branch 393 (VisitTree.branch 381 (VisitTree.leaf 371 [1]) (VisitTree.branch 385 (VisitTree.leaf 381 [1, 1]) (VisitTree.leaf 385 [1, 1]))) (VisitTree.branch 399 (VisitTree.leaf 393 [1]) (VisitTree.branch 404 (VisitTree.leaf 399 [1]) (VisitTree.leaf 404 [1]))))))) (VisitTree.branch 470 (VisitTree.branch 450 (VisitTree.branch 433 (VisitTree.branch 413 (VisitTree.branch 410 (VisitTree.leaf 408 [1]) (VisitTree.leaf 410 [1])) (VisitTree.branch 414 (VisitTree.leaf 413 [1, 1]) (VisitTree.branch 416 (VisitTree.leaf 414 [1]) (VisitTree.leaf 416 [1])))) (VisitTree.branch 444 (VisitTree.branch 436 (VisitTree.leaf 433 [1, 1]) (VisitTree.leaf 436 [1])) (VisitTree.branch 447 (VisitTree.leaf 444 [1, 1]) (VisitTree.branch 449 (VisitTree.leaf 447 [1]) (VisitTree.leaf 449 [1]))))) (VisitTree.branch 464 (VisitTree.branch 461 (VisitTree.branch 460 (VisitTree.leaf 450 [1]) (VisitTree.leaf 460 [1])) (VisitTree.branch 462 (VisitTree.leaf 461 [1]) (VisitTree.branch 463 (VisitTree.leaf 462 [1]) (VisitTree.leaf 463 [1, 1])))) (VisitTree.branch 466 (VisitTree.branch 465 (VisitTree.leaf 464 [1, 1]) (VisitTree.leaf 465 [1])) (VisitTree.branch 467 (VisitTree.leaf 466 [1, 1]) (VisitTree.branch 468 (VisitTree.leaf 467 [1]) (VisitTree.leaf 468 [1])))))) (VisitTree.branch 647 (VisitTree.branch 637 (VisitTree.branch 610 (VisitTree.branch 471 (VisitTree.leaf 470 [1]) (VisitTree.leaf 471 [1, 1])) (VisitTree.branch 623 (VisitTree.leaf 610 [1]) (VisitTree.branch 628 (VisitTree.leaf 623 [1]) (VisitTree.leaf 628 [1])))) (VisitTree.branch 644 (VisitTree.branch 643 (VisitTree.leaf 637 [1]) (VisitTree.leaf 643 [1])) (VisitTree.branch 645 (VisitTree.leaf 644 [1]) (VisitTree.branch 646 (VisitTree.leaf 645 [1]) (VisitTree.leaf 646 [1]))))) (VisitTree.branch 652 (VisitTree.branch 649 (VisitTree.branch 648 (VisitTree.leaf 647 [1]) (VisitTree.leaf 648 [1])) (VisitTree.branch 650 (VisitTree.leaf 649 [1]) (VisitTree.branch 651 (VisitTree.leaf 650 [1]) (VisitTree.leaf 651 [1])))) (VisitTree.branch 657 (VisitTree.branch 654 (VisitTree.leaf 652 [1]) (VisitTree.branch 656 (VisitTree.leaf 654 [1]) (VisitTree.leaf 656 [1]))) (VisitTree.branch 658 (VisitTree.leaf 657 [1]) (VisitTree.branch 659 (VisitTree.leaf 658 [1]) (VisitTree.leaf 659 [1]))))))))

def fastForwardChunkVisits115 (r : Nat) : List Nat :=
  forwardVisitTree115.lookup r

private theorem covered115 :
    visitsCovered forwardEventChunk115 forwardVisitTree115 = true := by
  decide +kernel

private theorem checked115 :
    visitsChecked forwardEventChunk115 forwardVisitTree115 = true := by
  decide +kernel

theorem eventVisits_forwardChunk115 (r : Nat) :
    eventVisits r forwardEventChunk115 = fastForwardChunkVisits115 r :=
  eventVisits_of_tree _ _ covered115 checked115 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk115


