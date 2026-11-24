-- Prove2me | Definitions.Def_CSL_Generated_MemoryAccess_Group05
-- name    : CSL_Generated_MemoryAccess_Group05
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T13:32:02.264214+00:00
-- url     : https://prove2.me/theorems/d0e80ff1-635c-4132-9851-3382a86e3405
-- title:
--   Coded sorting library: Generated / MemoryAccess / Group05
-- statement:
--   Module `CodedSorting.Generated.MemoryAccess.Group05` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Generated.MemoryAccess.Group05

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Circuit_MemoryAccess_PhysicalFrameEventChunkData
import Definitions.Def_CSL_Generated_MemoryAccess_Base

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 84. -/
def forwardVisitTree084 : VisitTree := (VisitTree.branch 60 (VisitTree.branch 33 (VisitTree.branch 17 (VisitTree.branch 13 (VisitTree.leaf 10 [521, 521, 521]) (VisitTree.leaf 13 [521])) (VisitTree.branch 22 (VisitTree.leaf 17 [509, 509, 509, 509, 509, 509]) (VisitTree.branch 32 (VisitTree.leaf 22 [509]) (VisitTree.leaf 32 [521])))) (VisitTree.branch 39 (VisitTree.branch 34 (VisitTree.leaf 33 [509, 509, 509, 509]) (VisitTree.branch 38 (VisitTree.leaf 34 [521]) (VisitTree.leaf 38 [509, 509, 509]))) (VisitTree.branch 42 (VisitTree.leaf 39 [521]) (VisitTree.branch 50 (VisitTree.leaf 42 [521]) (VisitTree.leaf 50 [509, 509, 509]))))) (VisitTree.branch 85 (VisitTree.branch 77 (VisitTree.branch 67 (VisitTree.leaf 60 [509, 509]) (VisitTree.branch 76 (VisitTree.leaf 67 [509, 509, 509]) (VisitTree.leaf 76 [521, 521]))) (VisitTree.branch 79 (VisitTree.leaf 77 [509, 509]) (VisitTree.branch 83 (VisitTree.leaf 79 [521, 521]) (VisitTree.leaf 83 [521, 521, 521, 521, 521, 521, 521, 521, 521, 521])))) (VisitTree.branch 104 (VisitTree.branch 87 (VisitTree.leaf 85 [521]) (VisitTree.branch 92 (VisitTree.leaf 87 [509, 509, 509, 509, 509, 509, 509, 509]) (VisitTree.leaf 92 [509, 509]))) (VisitTree.branch 107 (VisitTree.leaf 104 [521]) (VisitTree.branch 468 (VisitTree.leaf 107 [521, 521]) (VisitTree.leaf 468 [509, 509, 509, 509]))))))

def fastForwardChunkVisits084 (r : Nat) : List Nat :=
  forwardVisitTree084.lookup r

private theorem covered084 :
    visitsCovered forwardEventChunk084 forwardVisitTree084 = true := by
  decide +kernel

private theorem checked084 :
    visitsChecked forwardEventChunk084 forwardVisitTree084 = true := by
  decide +kernel

theorem eventVisits_forwardChunk084 (r : Nat) :
    eventVisits r forwardEventChunk084 = fastForwardChunkVisits084 r :=
  eventVisits_of_tree _ _ covered084 checked084 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk084

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 85. -/
def forwardVisitTree085 : VisitTree := (VisitTree.branch 76 (VisitTree.branch 34 (VisitTree.branch 13 (VisitTree.leaf 10 [521, 521, 521]) (VisitTree.branch 32 (VisitTree.leaf 13 [521, 521, 521, 521, 521, 521]) (VisitTree.leaf 32 [521, 521, 521]))) (VisitTree.branch 39 (VisitTree.leaf 34 [521, 521, 521, 521, 521, 521, 521]) (VisitTree.branch 42 (VisitTree.leaf 39 [521, 521, 521]) (VisitTree.leaf 42 [521, 521, 521, 521, 521, 521])))) (VisitTree.branch 85 (VisitTree.branch 79 (VisitTree.leaf 76 [521, 521, 521, 521]) (VisitTree.branch 83 (VisitTree.leaf 79 [521, 521, 521, 521, 521, 521]) (VisitTree.leaf 83 [521, 521, 521, 521, 521, 521, 521, 521]))) (VisitTree.branch 104 (VisitTree.leaf 85 [521, 521, 521, 521]) (VisitTree.branch 107 (VisitTree.leaf 104 [521, 521, 521, 521, 521, 521, 521]) (VisitTree.leaf 107 [521, 521, 521, 521, 521, 521, 521])))))

def fastForwardChunkVisits085 (r : Nat) : List Nat :=
  forwardVisitTree085.lookup r

private theorem covered085 :
    visitsCovered forwardEventChunk085 forwardVisitTree085 = true := by
  decide +kernel

private theorem checked085 :
    visitsChecked forwardEventChunk085 forwardVisitTree085 = true := by
  decide +kernel

theorem eventVisits_forwardChunk085 (r : Nat) :
    eventVisits r forwardEventChunk085 = fastForwardChunkVisits085 r :=
  eventVisits_of_tree _ _ covered085 checked085 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk085

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 86. -/
def forwardVisitTree086 : VisitTree := (VisitTree.branch 79 (VisitTree.branch 24 (VisitTree.branch 7 (VisitTree.leaf 1 [522, 522]) (VisitTree.branch 10 (VisitTree.leaf 7 [522, 522, 522, 522, 522, 522]) (VisitTree.leaf 10 [521, 521]))) (VisitTree.branch 28 (VisitTree.branch 25 (VisitTree.leaf 24 [522, 522, 522]) (VisitTree.leaf 25 [522, 522, 522, 522, 522, 522])) (VisitTree.branch 29 (VisitTree.leaf 28 [522, 522, 522, 522, 522, 522, 522, 522, 522, 522, 522, 522, 522, 522]) (VisitTree.leaf 29 [522, 522, 522, 522, 522])))) (VisitTree.branch 100 (VisitTree.branch 98 (VisitTree.branch 83 (VisitTree.leaf 79 [521]) (VisitTree.leaf 83 [521])) (VisitTree.branch 99 (VisitTree.leaf 98 [522, 522, 522, 522]) (VisitTree.leaf 99 [522, 522, 522]))) (VisitTree.branch 106 (VisitTree.branch 101 (VisitTree.leaf 100 [522, 522]) (VisitTree.leaf 101 [522, 522, 522, 522])) (VisitTree.branch 108 (VisitTree.leaf 106 [522]) (VisitTree.leaf 108 [522, 522, 522, 522, 522, 522, 522, 522, 522, 522])))))

def fastForwardChunkVisits086 (r : Nat) : List Nat :=
  forwardVisitTree086.lookup r

private theorem covered086 :
    visitsCovered forwardEventChunk086 forwardVisitTree086 = true := by
  decide +kernel

private theorem checked086 :
    visitsChecked forwardEventChunk086 forwardVisitTree086 = true := by
  decide +kernel

theorem eventVisits_forwardChunk086 (r : Nat) :
    eventVisits r forwardEventChunk086 = fastForwardChunkVisits086 r :=
  eventVisits_of_tree _ _ covered086 checked086 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk086

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 87. -/
def forwardVisitTree087 : VisitTree := (VisitTree.branch 29 (VisitTree.branch 16 (VisitTree.branch 4 (VisitTree.branch 2 (VisitTree.leaf 1 [522, 522, 522, 522]) (VisitTree.leaf 2 [523, 523, 523, 523, 523])) (VisitTree.branch 7 (VisitTree.leaf 4 [523, 523]) (VisitTree.branch 14 (VisitTree.leaf 7 [522, 522]) (VisitTree.leaf 14 [523])))) (VisitTree.branch 20 (VisitTree.branch 18 (VisitTree.leaf 16 [523, 523, 523]) (VisitTree.leaf 18 [523, 523, 523, 523, 523])) (VisitTree.branch 24 (VisitTree.leaf 20 [523, 523, 523, 523]) (VisitTree.branch 28 (VisitTree.leaf 24 [522]) (VisitTree.leaf 28 [522, 522, 522, 522, 522, 522]))))) (VisitTree.branch 99 (VisitTree.branch 90 (VisitTree.branch 88 (VisitTree.leaf 29 [522, 522, 522, 522]) (VisitTree.leaf 88 [523, 523, 523])) (VisitTree.branch 93 (VisitTree.leaf 90 [523]) (VisitTree.branch 95 (VisitTree.leaf 93 [523, 523, 523]) (VisitTree.leaf 95 [523, 523])))) (VisitTree.branch 103 (VisitTree.branch 100 (VisitTree.leaf 99 [522]) (VisitTree.branch 101 (VisitTree.leaf 100 [522, 522]) (VisitTree.leaf 101 [522, 522, 522]))) (VisitTree.branch 106 (VisitTree.leaf 103 [523, 523, 523, 523, 523, 523, 523]) (VisitTree.branch 109 (VisitTree.leaf 106 [522, 522, 522]) (VisitTree.leaf 109 [523, 523]))))))

def fastForwardChunkVisits087 (r : Nat) : List Nat :=
  forwardVisitTree087.lookup r

private theorem covered087 :
    visitsCovered forwardEventChunk087 forwardVisitTree087 = true := by
  decide +kernel

private theorem checked087 :
    visitsChecked forwardEventChunk087 forwardVisitTree087 = true := by
  decide +kernel

theorem eventVisits_forwardChunk087 (r : Nat) :
    eventVisits r forwardEventChunk087 = fastForwardChunkVisits087 r :=
  eventVisits_of_tree _ _ covered087 checked087 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk087

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 88. -/
def forwardVisitTree088 : VisitTree := (VisitTree.branch 78 (VisitTree.branch 16 (VisitTree.branch 8 (VisitTree.branch 4 (VisitTree.leaf 2 [523, 523, 523]) (VisitTree.leaf 4 [523, 523])) (VisitTree.branch 14 (VisitTree.leaf 8 [524]) (VisitTree.leaf 14 [523, 523, 523, 523, 523]))) (VisitTree.branch 20 (VisitTree.branch 18 (VisitTree.leaf 16 [523, 523]) (VisitTree.leaf 18 [523, 523, 523])) (VisitTree.branch 31 (VisitTree.leaf 20 [523, 523, 523, 523, 523, 523, 523, 523, 523, 523]) (VisitTree.branch 37 (VisitTree.leaf 31 [524]) (VisitTree.leaf 37 [524]))))) (VisitTree.branch 93 (VisitTree.branch 86 (VisitTree.branch 81 (VisitTree.leaf 78 [524]) (VisitTree.leaf 81 [524])) (VisitTree.branch 88 (VisitTree.leaf 86 [524]) (VisitTree.branch 90 (VisitTree.leaf 88 [523, 523, 523, 523, 523, 523]) (VisitTree.leaf 90 [523, 523])))) (VisitTree.branch 103 (VisitTree.branch 95 (VisitTree.leaf 93 [523, 523, 523, 523]) (VisitTree.leaf 95 [523, 523, 523])) (VisitTree.branch 109 (VisitTree.leaf 103 [523, 523, 523, 523, 523, 523, 523, 523, 523]) (VisitTree.branch 110 (VisitTree.leaf 109 [523, 523, 523]) (VisitTree.leaf 110 [524, 524, 524, 524, 524, 524]))))))

def fastForwardChunkVisits088 (r : Nat) : List Nat :=
  forwardVisitTree088.lookup r

private theorem covered088 :
    visitsCovered forwardEventChunk088 forwardVisitTree088 = true := by
  decide +kernel

private theorem checked088 :
    visitsChecked forwardEventChunk088 forwardVisitTree088 = true := by
  decide +kernel

theorem eventVisits_forwardChunk088 (r : Nat) :
    eventVisits r forwardEventChunk088 = fastForwardChunkVisits088 r :=
  eventVisits_of_tree _ _ covered088 checked088 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk088

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 89. -/
def forwardVisitTree089 : VisitTree := (VisitTree.branch 73 (VisitTree.branch 37 (VisitTree.branch 12 (VisitTree.leaf 8 [524, 524, 524, 524, 524]) (VisitTree.branch 31 (VisitTree.leaf 12 [524, 524, 524]) (VisitTree.leaf 31 [524, 524, 524, 524, 524, 524]))) (VisitTree.branch 40 (VisitTree.leaf 37 [524, 524, 524, 524]) (VisitTree.branch 45 (VisitTree.leaf 40 [524, 524, 524, 524, 524, 524, 524, 524, 524, 524]) (VisitTree.leaf 45 [524])))) (VisitTree.branch 86 (VisitTree.branch 78 (VisitTree.leaf 73 [524, 524, 524, 524, 524, 524]) (VisitTree.branch 81 (VisitTree.leaf 78 [524, 524, 524, 524, 524]) (VisitTree.leaf 81 [524, 524, 524]))) (VisitTree.branch 105 (VisitTree.leaf 86 [524, 524, 524, 524, 524]) (VisitTree.branch 110 (VisitTree.leaf 105 [524, 524, 524, 524, 524, 524, 524]) (VisitTree.leaf 110 [524, 524, 524, 524, 524, 524, 524, 524, 524])))))

def fastForwardChunkVisits089 (r : Nat) : List Nat :=
  forwardVisitTree089.lookup r

private theorem covered089 :
    visitsCovered forwardEventChunk089 forwardVisitTree089 = true := by
  decide +kernel

private theorem checked089 :
    visitsChecked forwardEventChunk089 forwardVisitTree089 = true := by
  decide +kernel

theorem eventVisits_forwardChunk089 (r : Nat) :
    eventVisits r forwardEventChunk089 = fastForwardChunkVisits089 r :=
  eventVisits_of_tree _ _ covered089 checked089 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk089

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 90. -/
def forwardVisitTree090 : VisitTree := (VisitTree.branch 109 (VisitTree.branch 62 (VisitTree.branch 28 (VisitTree.branch 9 (VisitTree.branch 2 (VisitTree.leaf 0 [326]) (VisitTree.branch 5 (VisitTree.leaf 2 [452]) (VisitTree.leaf 5 [344]))) (VisitTree.branch 23 (VisitTree.branch 21 (VisitTree.leaf 9 [345]) (VisitTree.leaf 21 [363])) (VisitTree.branch 25 (VisitTree.leaf 23 [398]) (VisitTree.leaf 25 [474])))) (VisitTree.branch 39 (VisitTree.branch 34 (VisitTree.branch 31 (VisitTree.leaf 28 [482]) (VisitTree.leaf 31 [524, 434])) (VisitTree.branch 35 (VisitTree.leaf 34 [488]) (VisitTree.leaf 35 [419]))) (VisitTree.branch 45 (VisitTree.branch 40 (VisitTree.leaf 39 [492]) (VisitTree.leaf 40 [524, 524])) (VisitTree.branch 48 (VisitTree.leaf 45 [524]) (VisitTree.leaf 48 [347]))))) (VisitTree.branch 94 (VisitTree.branch 87 (VisitTree.branch 69 (VisitTree.leaf 62 [327]) (VisitTree.branch 73 (VisitTree.leaf 69 [329]) (VisitTree.leaf 73 [437]))) (VisitTree.branch 92 (VisitTree.branch 91 (VisitTree.leaf 87 [384]) (VisitTree.leaf 91 [400])) (VisitTree.branch 93 (VisitTree.leaf 92 [381]) (VisitTree.leaf 93 [454])))) (VisitTree.branch 100 (VisitTree.branch 97 (VisitTree.branch 95 (VisitTree.leaf 94 [362]) (VisitTree.leaf 95 [466])) (VisitTree.branch 99 (VisitTree.leaf 97 [416]) (VisitTree.leaf 99 [471]))) (VisitTree.branch 103 (VisitTree.branch 101 (VisitTree.leaf 100 [476]) (VisitTree.leaf 101 [484])) (VisitTree.branch 106 (VisitTree.leaf 103 [464]) (VisitTree.leaf 106 [477])))))) (VisitTree.branch 461 (VisitTree.branch 272 (VisitTree.branch 243 (VisitTree.branch 110 (VisitTree.leaf 109 [459]) (VisitTree.branch 235 (VisitTree.leaf 110 [524, 524]) (VisitTree.leaf 235 [327]))) (VisitTree.branch 255 (VisitTree.branch 247 (VisitTree.leaf 243 [344]) (VisitTree.leaf 247 [326])) (VisitTree.branch 262 (VisitTree.leaf 255 [466]) (VisitTree.leaf 262 [484])))) (VisitTree.branch 429 (VisitTree.branch 425 (VisitTree.branch 419 (VisitTree.leaf 272 [347]) (VisitTree.leaf 419 [464])) (VisitTree.branch 427 (VisitTree.leaf 425 [482]) (VisitTree.leaf 427 [398]))) (VisitTree.branch 439 (VisitTree.branch 437 (VisitTree.leaf 429 [477]) (VisitTree.leaf 437 [416])) (VisitTree.branch 457 (VisitTree.leaf 439 [476]) (VisitTree.leaf 457 [452]))))) (VisitTree.branch 539 (VisitTree.branch 502 (VisitTree.branch 485 (VisitTree.branch 481 (VisitTree.leaf 461 [488]) (VisitTree.leaf 481 [434])) (VisitTree.branch 501 (VisitTree.leaf 485 [345]) (VisitTree.leaf 501 [329]))) (VisitTree.branch 521 (VisitTree.branch 518 (VisitTree.leaf 502 [362]) (VisitTree.leaf 518 [384])) (VisitTree.branch 537 (VisitTree.leaf 521 [381]) (VisitTree.leaf 537 [419])))) (VisitTree.branch 618 (VisitTree.branch 568 (VisitTree.branch 556 (VisitTree.leaf 539 [363]) (VisitTree.leaf 556 [400])) (VisitTree.branch 611 (VisitTree.leaf 568 [459]) (VisitTree.leaf 611 [474]))) (VisitTree.branch 629 (VisitTree.branch 627 (VisitTree.leaf 618 [437]) (VisitTree.leaf 627 [454])) (VisitTree.branch 644 (VisitTree.leaf 629 [471]) (VisitTree.leaf 644 [492])))))))

def fastForwardChunkVisits090 (r : Nat) : List Nat :=
  forwardVisitTree090.lookup r

private theorem covered090 :
    visitsCovered forwardEventChunk090 forwardVisitTree090 = true := by
  decide +kernel

private theorem checked090 :
    visitsChecked forwardEventChunk090 forwardVisitTree090 = true := by
  decide +kernel

theorem eventVisits_forwardChunk090 (r : Nat) :
    eventVisits r forwardEventChunk090 = fastForwardChunkVisits090 r :=
  eventVisits_of_tree _ _ covered090 checked090 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk090

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 91. -/
def forwardVisitTree091 : VisitTree := (VisitTree.branch 251 (VisitTree.branch 63 (VisitTree.branch 38 (VisitTree.branch 17 (VisitTree.branch 15 (VisitTree.branch 11 (VisitTree.leaf 3 [337]) (VisitTree.leaf 11 [338])) (VisitTree.branch 16 (VisitTree.leaf 15 [413]) (VisitTree.leaf 16 [462]))) (VisitTree.branch 32 (VisitTree.branch 27 (VisitTree.leaf 17 [395]) (VisitTree.leaf 27 [425])) (VisitTree.branch 36 (VisitTree.leaf 32 [504]) (VisitTree.leaf 36 [369])))) (VisitTree.branch 45 (VisitTree.branch 42 (VisitTree.branch 41 (VisitTree.leaf 38 [389]) (VisitTree.leaf 41 [404])) (VisitTree.branch 43 (VisitTree.leaf 42 [496]) (VisitTree.leaf 43 [422]))) (VisitTree.branch 51 (VisitTree.branch 49 (VisitTree.leaf 45 [440]) (VisitTree.leaf 49 [405])) (VisitTree.branch 61 (VisitTree.leaf 51 [375]) (VisitTree.leaf 61 [343]))))) (VisitTree.branch 78 (VisitTree.branch 71 (VisitTree.branch 65 (VisitTree.branch 64 (VisitTree.leaf 63 [342]) (VisitTree.leaf 64 [379])) (VisitTree.branch 68 (VisitTree.leaf 65 [433]) (VisitTree.leaf 68 [334]))) (VisitTree.branch 76 (VisitTree.branch 72 (VisitTree.leaf 71 [377]) (VisitTree.leaf 72 [333])) (VisitTree.branch 77 (VisitTree.leaf 76 [494]) (VisitTree.leaf 77 [386])))) (VisitTree.branch 86 (VisitTree.branch 81 (VisitTree.branch 79 (VisitTree.leaf 78 [446]) (VisitTree.leaf 79 [500])) (VisitTree.branch 82 (VisitTree.leaf 81 [448]) (VisitTree.leaf 82 [410]))) (VisitTree.branch 102 (VisitTree.branch 89 (VisitTree.leaf 86 [443]) (VisitTree.leaf 89 [429])) (VisitTree.branch 232 (VisitTree.leaf 102 [368]) (VisitTree.leaf 232 [379])))))) (VisitTree.branch 414 (VisitTree.branch 345 (VisitTree.branch 282 (VisitTree.branch 256 (VisitTree.branch 253 (VisitTree.leaf 251 [377]) (VisitTree.leaf 253 [368])) (VisitTree.branch 275 (VisitTree.leaf 256 [334]) (VisitTree.leaf 275 [462]))) (VisitTree.branch 326 (VisitTree.branch 323 (VisitTree.leaf 282 [504]) (VisitTree.leaf 323 [339])) (VisitTree.branch 334 (VisitTree.leaf 326 [337]) (VisitTree.leaf 334 [433])))) (VisitTree.branch 379 (VisitTree.branch 374 (VisitTree.branch 373 (VisitTree.leaf 345 [333]) (VisitTree.leaf 373 [338])) (VisitTree.branch 378 (VisitTree.leaf 374 [448]) (VisitTree.leaf 378 [413]))) (VisitTree.branch 401 (VisitTree.branch 389 (VisitTree.leaf 379 [410]) (VisitTree.leaf 389 [404])) (VisitTree.branch 405 (VisitTree.leaf 401 [422]) (VisitTree.leaf 405 [386]))))) (VisitTree.branch 527 (VisitTree.branch 465 (VisitTree.branch 453 (VisitTree.branch 432 (VisitTree.leaf 414 [496]) (VisitTree.leaf 432 [342])) (VisitTree.branch 456 (VisitTree.leaf 453 [429]) (VisitTree.leaf 456 [375]))) (VisitTree.branch 511 (VisitTree.branch 492 (VisitTree.leaf 465 [339]) (VisitTree.leaf 492 [395])) (VisitTree.branch 526 (VisitTree.leaf 511 [343]) (VisitTree.leaf 526 [389])))) (VisitTree.branch 589 (VisitTree.branch 578 (VisitTree.branch 563 (VisitTree.leaf 527 [440]) (VisitTree.leaf 563 [405])) (VisitTree.branch 588 (VisitTree.leaf 578 [446]) (VisitTree.leaf 588 [443]))) (VisitTree.branch 628 (VisitTree.branch 600 (VisitTree.leaf 589 [425]) (VisitTree.leaf 600 [369])) (VisitTree.branch 654 (VisitTree.leaf 628 [500]) (VisitTree.leaf 654 [494])))))))

def fastForwardChunkVisits091 (r : Nat) : List Nat :=
  forwardVisitTree091.lookup r

private theorem covered091 :
    visitsCovered forwardEventChunk091 forwardVisitTree091 = true := by
  decide +kernel

private theorem checked091 :
    visitsChecked forwardEventChunk091 forwardVisitTree091 = true := by
  decide +kernel

theorem eventVisits_forwardChunk091 (r : Nat) :
    eventVisits r forwardEventChunk091 = fastForwardChunkVisits091 r :=
  eventVisits_of_tree _ _ covered091 checked091 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk091

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 92. -/
def forwardVisitTree092 : VisitTree := (VisitTree.branch 258 (VisitTree.branch 56 (VisitTree.branch 44 (VisitTree.branch 29 (VisitTree.branch 24 (VisitTree.branch 13 (VisitTree.leaf 12 [442]) (VisitTree.leaf 13 [503])) (VisitTree.branch 26 (VisitTree.leaf 24 [487]) (VisitTree.leaf 26 [373]))) (VisitTree.branch 33 (VisitTree.branch 30 (VisitTree.leaf 29 [479]) (VisitTree.leaf 30 [415])) (VisitTree.branch 37 (VisitTree.leaf 33 [383]) (VisitTree.leaf 37 [450])))) (VisitTree.branch 52 (VisitTree.branch 47 (VisitTree.branch 46 (VisitTree.leaf 44 [370]) (VisitTree.leaf 46 [354])) (VisitTree.branch 50 (VisitTree.leaf 47 [356]) (VisitTree.leaf 50 [397]))) (VisitTree.branch 54 (VisitTree.branch 53 (VisitTree.leaf 52 [358]) (VisitTree.leaf 53 [414])) (VisitTree.branch 55 (VisitTree.leaf 54 [355]) (VisitTree.leaf 55 [365]))))) (VisitTree.branch 75 (VisitTree.branch 66 (VisitTree.branch 58 (VisitTree.branch 57 (VisitTree.leaf 56 [353]) (VisitTree.leaf 57 [430])) (VisitTree.branch 60 (VisitTree.leaf 58 [360]) (VisitTree.leaf 60 [396]))) (VisitTree.branch 70 (VisitTree.branch 67 (VisitTree.leaf 66 [417]) (VisitTree.leaf 67 [387])) (VisitTree.branch 74 (VisitTree.leaf 70 [409]) (VisitTree.leaf 74 [423])))) (VisitTree.branch 105 (VisitTree.branch 84 (VisitTree.branch 83 (VisitTree.leaf 75 [407]) (VisitTree.leaf 83 [498])) (VisitTree.branch 85 (VisitTree.leaf 84 [378]) (VisitTree.leaf 85 [502]))) (VisitTree.branch 110 (VisitTree.branch 107 (VisitTree.leaf 105 [451]) (VisitTree.leaf 107 [495])) (VisitTree.branch 225 (VisitTree.leaf 110 [445]) (VisitTree.leaf 225 [396])))))) (VisitTree.branch 491 (VisitTree.branch 342 (VisitTree.branch 304 (VisitTree.branch 301 (VisitTree.branch 298 (VisitTree.leaf 258 [487]) (VisitTree.leaf 298 [409])) (VisitTree.branch 302 (VisitTree.leaf 301 [495]) (VisitTree.leaf 302 [445]))) (VisitTree.branch 324 (VisitTree.branch 312 (VisitTree.leaf 304 [451]) (VisitTree.leaf 312 [353])) (VisitTree.branch 336 (VisitTree.leaf 324 [355]) (VisitTree.leaf 336 [358])))) (VisitTree.branch 392 (VisitTree.branch 347 (VisitTree.branch 346 (VisitTree.leaf 342 [397]) (VisitTree.leaf 346 [415])) (VisitTree.branch 362 (VisitTree.leaf 347 [356]) (VisitTree.leaf 362 [414]))) (VisitTree.branch 454 (VisitTree.branch 404 (VisitTree.leaf 392 [442]) (VisitTree.leaf 404 [503])) (VisitTree.branch 466 (VisitTree.leaf 454 [430]) (VisitTree.leaf 466 [424]))))) (VisitTree.branch 573 (VisitTree.branch 543 (VisitTree.branch 500 (VisitTree.branch 494 (VisitTree.leaf 491 [354]) (VisitTree.leaf 494 [360])) (VisitTree.branch 505 (VisitTree.leaf 500 [373]) (VisitTree.leaf 505 [378]))) (VisitTree.branch 555 (VisitTree.branch 544 (VisitTree.leaf 543 [370]) (VisitTree.leaf 544 [407])) (VisitTree.branch 565 (VisitTree.leaf 555 [365]) (VisitTree.leaf 565 [450])))) (VisitTree.branch 607 (VisitTree.branch 594 (VisitTree.branch 581 (VisitTree.leaf 573 [383]) (VisitTree.leaf 581 [423])) (VisitTree.branch 601 (VisitTree.leaf 594 [424]) (VisitTree.leaf 601 [387]))) (VisitTree.branch 650 (VisitTree.branch 633 (VisitTree.leaf 607 [417]) (VisitTree.leaf 633 [479])) (VisitTree.branch 658 (VisitTree.leaf 650 [498]) (VisitTree.leaf 658 [502])))))))

def fastForwardChunkVisits092 (r : Nat) : List Nat :=
  forwardVisitTree092.lookup r

private theorem covered092 :
    visitsCovered forwardEventChunk092 forwardVisitTree092 = true := by
  decide +kernel

private theorem checked092 :
    visitsChecked forwardEventChunk092 forwardVisitTree092 = true := by
  decide +kernel

theorem eventVisits_forwardChunk092 (r : Nat) :
    eventVisits r forwardEventChunk092 = fastForwardChunkVisits092 r :=
  eventVisits_of_tree _ _ covered092 checked092 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk092

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 93. -/
def forwardVisitTree093 : VisitTree := (VisitTree.branch 123 (VisitTree.branch 73 (VisitTree.branch 18 (VisitTree.branch 7 (VisitTree.branch 2 (VisitTree.branch 1 (VisitTree.leaf 0 [531]) (VisitTree.leaf 1 [472])) (VisitTree.branch 4 (VisitTree.leaf 2 [532]) (VisitTree.branch 5 (VisitTree.leaf 4 [457]) (VisitTree.leaf 5 [528])))) (VisitTree.branch 9 (VisitTree.branch 8 (VisitTree.leaf 7 [473]) (VisitTree.leaf 8 [436])) (VisitTree.branch 10 (VisitTree.leaf 9 [525]) (VisitTree.branch 14 (VisitTree.leaf 10 [493]) (VisitTree.leaf 14 [468]))))) (VisitTree.branch 39 (VisitTree.branch 25 (VisitTree.branch 20 (VisitTree.leaf 18 [460]) (VisitTree.leaf 20 [453])) (VisitTree.branch 31 (VisitTree.leaf 25 [529]) (VisitTree.branch 34 (VisitTree.leaf 31 [535]) (VisitTree.leaf 34 [533])))) (VisitTree.branch 59 (VisitTree.branch 40 (VisitTree.leaf 39 [537]) (VisitTree.branch 48 (VisitTree.leaf 40 [435]) (VisitTree.leaf 48 [536]))) (VisitTree.branch 62 (VisitTree.leaf 59 [402]) (VisitTree.branch 69 (VisitTree.leaf 62 [530]) (VisitTree.leaf 69 [534])))))) (VisitTree.branch 112 (VisitTree.branch 96 (VisitTree.branch 88 (VisitTree.branch 80 (VisitTree.leaf 73 [538]) (VisitTree.leaf 80 [366])) (VisitTree.branch 90 (VisitTree.leaf 88 [463]) (VisitTree.branch 93 (VisitTree.leaf 90 [467]) (VisitTree.leaf 93 [526])))) (VisitTree.branch 104 (VisitTree.branch 98 (VisitTree.leaf 96 [403]) (VisitTree.branch 99 (VisitTree.leaf 98 [480]) (VisitTree.leaf 99 [527]))) (VisitTree.branch 108 (VisitTree.leaf 104 [489]) (VisitTree.branch 111 (VisitTree.leaf 108 [486]) (VisitTree.leaf 111 [525]))))) (VisitTree.branch 117 (VisitTree.branch 114 (VisitTree.branch 113 (VisitTree.leaf 112 [526]) (VisitTree.leaf 113 [527])) (VisitTree.branch 115 (VisitTree.leaf 114 [528]) (VisitTree.branch 116 (VisitTree.leaf 115 [529]) (VisitTree.leaf 116 [530])))) (VisitTree.branch 120 (VisitTree.branch 118 (VisitTree.leaf 117 [531]) (VisitTree.branch 119 (VisitTree.leaf 118 [532]) (VisitTree.leaf 119 [533]))) (VisitTree.branch 121 (VisitTree.leaf 120 [534]) (VisitTree.branch 122 (VisitTree.leaf 121 [535]) (VisitTree.leaf 122 [536]))))))) (VisitTree.branch 461 (VisitTree.branch 247 (VisitTree.branch 235 (VisitTree.branch 223 (VisitTree.branch 124 (VisitTree.leaf 123 [537]) (VisitTree.leaf 124 [538])) (VisitTree.branch 228 (VisitTree.leaf 223 [528]) (VisitTree.branch 234 (VisitTree.leaf 228 [531]) (VisitTree.leaf 234 [530])))) (VisitTree.branch 238 (VisitTree.branch 236 (VisitTree.leaf 235 [534]) (VisitTree.leaf 236 [457])) (VisitTree.branch 243 (VisitTree.leaf 238 [493]) (VisitTree.branch 246 (VisitTree.leaf 243 [525]) (VisitTree.leaf 246 [525]))))) (VisitTree.branch 311 (VisitTree.branch 268 (VisitTree.branch 260 (VisitTree.leaf 247 [530]) (VisitTree.leaf 260 [463])) (VisitTree.branch 272 (VisitTree.leaf 268 [403]) (VisitTree.branch 274 (VisitTree.leaf 272 [528]) (VisitTree.leaf 274 [385])))) (VisitTree.branch 436 (VisitTree.branch 322 (VisitTree.leaf 311 [533]) (VisitTree.branch 382 (VisitTree.leaf 322 [536]) (VisitTree.leaf 382 [538]))) (VisitTree.branch 447 (VisitTree.leaf 436 [527]) (VisitTree.branch 457 (VisitTree.leaf 447 [529]) (VisitTree.leaf 457 [526])))))) (VisitTree.branch 613 (VisitTree.branch 504 (VisitTree.branch 481 (VisitTree.branch 468 (VisitTree.leaf 461 [537]) (VisitTree.leaf 468 [385])) (VisitTree.branch 485 (VisitTree.leaf 481 [538]) (VisitTree.branch 501 (VisitTree.leaf 485 [536]) (VisitTree.leaf 501 [531])))) (VisitTree.branch 608 (VisitTree.branch 536 (VisitTree.leaf 504 [534]) (VisitTree.branch 586 (VisitTree.leaf 536 [366]) (VisitTree.leaf 586 [467]))) (VisitTree.branch 609 (VisitTree.leaf 608 [532]) (VisitTree.branch 612 (VisitTree.leaf 609 [472, 527]) (VisitTree.leaf 612 [402]))))) (VisitTree.branch 632 (VisitTree.branch 620 (VisitTree.branch 616 (VisitTree.leaf 613 [436, 535]) (VisitTree.leaf 616 [460])) (VisitTree.branch 624 (VisitTree.leaf 620 [468]) (VisitTree.branch 626 (VisitTree.leaf 624 [435, 535]) (VisitTree.leaf 626 [453, 526])))) (VisitTree.branch 647 (VisitTree.branch 638 (VisitTree.leaf 632 [480]) (VisitTree.branch 645 (VisitTree.leaf 638 [486]) (VisitTree.leaf 645 [537]))) (VisitTree.branch 655 (VisitTree.leaf 647 [489, 533]) (VisitTree.branch 660 (VisitTree.leaf 655 [473, 529]) (VisitTree.leaf 660 [532]))))))))

def fastForwardChunkVisits093 (r : Nat) : List Nat :=
  forwardVisitTree093.lookup r

private theorem covered093 :
    visitsCovered forwardEventChunk093 forwardVisitTree093 = true := by
  decide +kernel

private theorem checked093 :
    visitsChecked forwardEventChunk093 forwardVisitTree093 = true := by
  decide +kernel

theorem eventVisits_forwardChunk093 (r : Nat) :
    eventVisits r forwardEventChunk093 = fastForwardChunkVisits093 r :=
  eventVisits_of_tree _ _ covered093 checked093 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk093

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 94. -/
def forwardVisitTree094 : VisitTree := (VisitTree.branch 237 (VisitTree.branch 125 (VisitTree.branch 78 (VisitTree.branch 38 (VisitTree.branch 28 (VisitTree.branch 23 (VisitTree.branch 21 (VisitTree.leaf 16 [554]) (VisitTree.leaf 21 [540])) (VisitTree.branch 27 (VisitTree.leaf 23 [551]) (VisitTree.leaf 27 [563]))) (VisitTree.branch 35 (VisitTree.branch 32 (VisitTree.leaf 28 [543]) (VisitTree.leaf 32 [570])) (VisitTree.branch 36 (VisitTree.leaf 35 [547]) (VisitTree.leaf 36 [555])))) (VisitTree.branch 45 (VisitTree.branch 42 (VisitTree.branch 41 (VisitTree.leaf 38 [568]) (VisitTree.leaf 41 [569])) (VisitTree.branch 43 (VisitTree.leaf 42 [556]) (VisitTree.leaf 43 [558]))) (VisitTree.branch 76 (VisitTree.branch 49 (VisitTree.leaf 45 [557]) (VisitTree.leaf 49 [561])) (VisitTree.branch 77 (VisitTree.leaf 76 [562]) (VisitTree.leaf 77 [560]))))) (VisitTree.branch 95 (VisitTree.branch 87 (VisitTree.branch 81 (VisitTree.branch 79 (VisitTree.leaf 78 [567]) (VisitTree.leaf 79 [565])) (VisitTree.branch 86 (VisitTree.leaf 81 [564]) (VisitTree.leaf 86 [559]))) (VisitTree.branch 92 (VisitTree.branch 91 (VisitTree.leaf 87 [552]) (VisitTree.leaf 91 [546])) (VisitTree.branch 94 (VisitTree.leaf 92 [544]) (VisitTree.leaf 94 [548])))) (VisitTree.branch 102 (VisitTree.branch 100 (VisitTree.branch 97 (VisitTree.leaf 95 [550]) (VisitTree.leaf 97 [542])) (VisitTree.branch 101 (VisitTree.leaf 100 [545]) (VisitTree.leaf 101 [541]))) (VisitTree.branch 106 (VisitTree.branch 103 (VisitTree.leaf 102 [566]) (VisitTree.leaf 103 [553])) (VisitTree.branch 109 (VisitTree.leaf 106 [539]) (VisitTree.leaf 109 [549])))))) (VisitTree.branch 141 (VisitTree.branch 133 (VisitTree.branch 129 (VisitTree.branch 127 (VisitTree.branch 126 (VisitTree.leaf 125 [539]) (VisitTree.leaf 126 [540])) (VisitTree.branch 128 (VisitTree.leaf 127 [541]) (VisitTree.leaf 128 [542]))) (VisitTree.branch 131 (VisitTree.branch 130 (VisitTree.leaf 129 [543]) (VisitTree.leaf 130 [544])) (VisitTree.branch 132 (VisitTree.leaf 131 [545]) (VisitTree.leaf 132 [546])))) (VisitTree.branch 137 (VisitTree.branch 135 (VisitTree.branch 134 (VisitTree.leaf 133 [547]) (VisitTree.leaf 134 [548])) (VisitTree.branch 136 (VisitTree.leaf 135 [549]) (VisitTree.leaf 136 [550]))) (VisitTree.branch 139 (VisitTree.branch 138 (VisitTree.leaf 137 [551]) (VisitTree.leaf 138 [552])) (VisitTree.branch 140 (VisitTree.leaf 139 [553]) (VisitTree.leaf 140 [554]))))) (VisitTree.branch 149 (VisitTree.branch 145 (VisitTree.branch 143 (VisitTree.branch 142 (VisitTree.leaf 141 [555]) (VisitTree.leaf 142 [556])) (VisitTree.branch 144 (VisitTree.leaf 143 [557]) (VisitTree.leaf 144 [558]))) (VisitTree.branch 147 (VisitTree.branch 146 (VisitTree.leaf 145 [559]) (VisitTree.leaf 146 [560])) (VisitTree.branch 148 (VisitTree.leaf 147 [561]) (VisitTree.leaf 148 [562])))) (VisitTree.branch 153 (VisitTree.branch 151 (VisitTree.branch 150 (VisitTree.leaf 149 [563]) (VisitTree.leaf 150 [564])) (VisitTree.branch 152 (VisitTree.leaf 151 [565]) (VisitTree.leaf 152 [566]))) (VisitTree.branch 155 (VisitTree.branch 154 (VisitTree.leaf 153 [567]) (VisitTree.leaf 154 [568])) (VisitTree.branch 156 (VisitTree.leaf 155 [569]) (VisitTree.leaf 156 [570]))))))) (VisitTree.branch 520 (VisitTree.branch 392 (VisitTree.branch 278 (VisitTree.branch 257 (VisitTree.branch 253 (VisitTree.branch 245 (VisitTree.leaf 237 [541]) (VisitTree.leaf 245 [562])) (VisitTree.branch 254 (VisitTree.leaf 253 [555]) (VisitTree.leaf 254 [550]))) (VisitTree.branch 271 (VisitTree.branch 267 (VisitTree.leaf 257 [546]) (VisitTree.leaf 267 [539])) (VisitTree.branch 273 (VisitTree.leaf 271 [544]) (VisitTree.leaf 273 [551])))) (VisitTree.branch 314 (VisitTree.branch 293 (VisitTree.branch 290 (VisitTree.leaf 278 [566]) (VisitTree.leaf 290 [565])) (VisitTree.branch 301 (VisitTree.leaf 293 [552]) (VisitTree.leaf 301 [556]))) (VisitTree.branch 367 (VisitTree.branch 327 (VisitTree.leaf 314 [554]) (VisitTree.leaf 327 [561])) (VisitTree.branch 389 (VisitTree.leaf 367 [557]) (VisitTree.leaf 389 [561]))))) (VisitTree.branch 427 (VisitTree.branch 416 (VisitTree.branch 404 (VisitTree.branch 401 (VisitTree.leaf 392 [557]) (VisitTree.leaf 401 [563])) (VisitTree.branch 405 (VisitTree.leaf 404 [570]) (VisitTree.leaf 405 [568]))) (VisitTree.branch 423 (VisitTree.branch 419 (VisitTree.leaf 416 [563]) (VisitTree.leaf 419 [550])) (VisitTree.branch 425 (VisitTree.leaf 423 [554]) (VisitTree.leaf 425 [541])))) (VisitTree.branch 445 (VisitTree.branch 437 (VisitTree.branch 433 (VisitTree.leaf 427 [546]) (VisitTree.leaf 433 [542])) (VisitTree.branch 439 (VisitTree.leaf 437 [547]) (VisitTree.leaf 439 [539]))) (VisitTree.branch 482 (VisitTree.branch 459 (VisitTree.leaf 445 [564]) (VisitTree.leaf 459 [549])) (VisitTree.branch 502 (VisitTree.leaf 482 [544]) (VisitTree.leaf 502 [540])))))) (VisitTree.branch 594 (VisitTree.branch 555 (VisitTree.branch 536 (VisitTree.branch 525 (VisitTree.branch 524 (VisitTree.leaf 520 [540]) (VisitTree.leaf 524 [569])) (VisitTree.branch 527 (VisitTree.leaf 525 [566]) (VisitTree.leaf 527 [559]))) (VisitTree.branch 544 (VisitTree.branch 543 (VisitTree.leaf 536 [548]) (VisitTree.leaf 543 [555])) (VisitTree.branch 554 (VisitTree.leaf 544 [569]) (VisitTree.leaf 554 [547])))) (VisitTree.branch 573 (VisitTree.branch 565 (VisitTree.branch 561 (VisitTree.leaf 555 [548]) (VisitTree.leaf 561 [560])) (VisitTree.branch 571 (VisitTree.leaf 565 [567]) (VisitTree.leaf 571 [559]))) (VisitTree.branch 581 (VisitTree.branch 578 (VisitTree.leaf 573 [552]) (VisitTree.leaf 578 [564])) (VisitTree.branch 586 (VisitTree.leaf 581 [558]) (VisitTree.leaf 586 [553]))))) (VisitTree.branch 628 (VisitTree.branch 607 (VisitTree.branch 603 (VisitTree.branch 601 (VisitTree.leaf 594 [558]) (VisitTree.leaf 601 [560])) (VisitTree.branch 606 (VisitTree.leaf 603 [567]) (VisitTree.leaf 606 [568]))) (VisitTree.branch 616 (VisitTree.branch 612 (VisitTree.leaf 607 [542]) (VisitTree.leaf 612 [551])) (VisitTree.branch 620 (VisitTree.leaf 616 [549]) (VisitTree.leaf 620 [553])))) (VisitTree.branch 639 (VisitTree.branch 633 (VisitTree.branch 632 (VisitTree.leaf 628 [570]) (VisitTree.leaf 632 [545])) (VisitTree.branch 638 (VisitTree.leaf 633 [545]) (VisitTree.leaf 638 [543]))) (VisitTree.branch 654 (VisitTree.branch 650 (VisitTree.leaf 639 [543]) (VisitTree.leaf 650 [562])) (VisitTree.branch 658 (VisitTree.leaf 654 [556]) (VisitTree.leaf 658 [565]))))))))

def fastForwardChunkVisits094 (r : Nat) : List Nat :=
  forwardVisitTree094.lookup r

private theorem covered094 :
    visitsCovered forwardEventChunk094 forwardVisitTree094 = true := by
  decide +kernel

private theorem checked094 :
    visitsChecked forwardEventChunk094 forwardVisitTree094 = true := by
  decide +kernel

theorem eventVisits_forwardChunk094 (r : Nat) :
    eventVisits r forwardEventChunk094 = fastForwardChunkVisits094 r :=
  eventVisits_of_tree _ _ covered094 checked094 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk094

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 95. -/
def forwardVisitTree095 : VisitTree := (VisitTree.branch 225 (VisitTree.branch 158 (VisitTree.branch 58 (VisitTree.branch 47 (VisitTree.branch 17 (VisitTree.branch 13 (VisitTree.branch 11 (VisitTree.leaf 3 [579]) (VisitTree.leaf 11 [572])) (VisitTree.branch 15 (VisitTree.leaf 13 [598]) (VisitTree.leaf 15 [580]))) (VisitTree.branch 30 (VisitTree.branch 26 (VisitTree.leaf 17 [582]) (VisitTree.leaf 26 [600])) (VisitTree.branch 46 (VisitTree.leaf 30 [589]) (VisitTree.leaf 46 [587])))) (VisitTree.branch 53 (VisitTree.branch 51 (VisitTree.branch 50 (VisitTree.leaf 47 [586]) (VisitTree.leaf 50 [590])) (VisitTree.branch 52 (VisitTree.leaf 51 [574]) (VisitTree.leaf 52 [593]))) (VisitTree.branch 56 (VisitTree.branch 54 (VisitTree.leaf 53 [596]) (VisitTree.leaf 54 [597])) (VisitTree.branch 57 (VisitTree.leaf 56 [594]) (VisitTree.leaf 57 [592]))))) (VisitTree.branch 71 (VisitTree.branch 64 (VisitTree.branch 61 (VisitTree.branch 60 (VisitTree.leaf 58 [588]) (VisitTree.leaf 60 [591])) (VisitTree.branch 63 (VisitTree.leaf 61 [583]) (VisitTree.leaf 63 [573]))) (VisitTree.branch 67 (VisitTree.branch 65 (VisitTree.leaf 64 [584]) (VisitTree.leaf 65 [585])) (VisitTree.branch 68 (VisitTree.leaf 67 [599]) (VisitTree.leaf 68 [581])))) (VisitTree.branch 84 (VisitTree.branch 74 (VisitTree.branch 72 (VisitTree.leaf 71 [578]) (VisitTree.leaf 72 [571])) (VisitTree.branch 82 (VisitTree.leaf 74 [602]) (VisitTree.leaf 82 [576]))) (VisitTree.branch 105 (VisitTree.branch 89 (VisitTree.leaf 84 [595]) (VisitTree.leaf 89 [575])) (VisitTree.branch 157 (VisitTree.leaf 105 [601]) (VisitTree.leaf 157 [571])))))) (VisitTree.branch 174 (VisitTree.branch 166 (VisitTree.branch 162 (VisitTree.branch 160 (VisitTree.branch 159 (VisitTree.leaf 158 [572]) (VisitTree.leaf 159 [573])) (VisitTree.branch 161 (VisitTree.leaf 160 [574]) (VisitTree.leaf 161 [575]))) (VisitTree.branch 164 (VisitTree.branch 163 (VisitTree.leaf 162 [576]) (VisitTree.leaf 163 [577])) (VisitTree.branch 165 (VisitTree.leaf 164 [578]) (VisitTree.leaf 165 [579])))) (VisitTree.branch 170 (VisitTree.branch 168 (VisitTree.branch 167 (VisitTree.leaf 166 [580]) (VisitTree.leaf 167 [581])) (VisitTree.branch 169 (VisitTree.leaf 168 [582]) (VisitTree.leaf 169 [583]))) (VisitTree.branch 172 (VisitTree.branch 171 (VisitTree.leaf 170 [584]) (VisitTree.leaf 171 [585])) (VisitTree.branch 173 (VisitTree.leaf 172 [586]) (VisitTree.leaf 173 [587]))))) (VisitTree.branch 182 (VisitTree.branch 178 (VisitTree.branch 176 (VisitTree.branch 175 (VisitTree.leaf 174 [588]) (VisitTree.leaf 175 [589])) (VisitTree.branch 177 (VisitTree.leaf 176 [590]) (VisitTree.leaf 177 [591]))) (VisitTree.branch 180 (VisitTree.branch 179 (VisitTree.leaf 178 [592]) (VisitTree.leaf 179 [593])) (VisitTree.branch 181 (VisitTree.leaf 180 [594]) (VisitTree.leaf 181 [595])))) (VisitTree.branch 186 (VisitTree.branch 184 (VisitTree.branch 183 (VisitTree.leaf 182 [596]) (VisitTree.leaf 183 [597])) (VisitTree.branch 185 (VisitTree.leaf 184 [598]) (VisitTree.leaf 185 [599]))) (VisitTree.branch 188 (VisitTree.branch 187 (VisitTree.leaf 186 [600]) (VisitTree.leaf 187 [601])) (VisitTree.branch 222 (VisitTree.leaf 188 [602]) (VisitTree.leaf 222 [578]))))))) (VisitTree.branch 363 (VisitTree.branch 332 (VisitTree.branch 305 (VisitTree.branch 251 (VisitTree.branch 232 (VisitTree.branch 229 (VisitTree.leaf 225 [582]) (VisitTree.leaf 229 [581])) (VisitTree.branch 250 (VisitTree.leaf 232 [595]) (VisitTree.leaf 250 [598]))) (VisitTree.branch 287 (VisitTree.branch 256 (VisitTree.leaf 251 [584]) (VisitTree.leaf 256 [571])) (VisitTree.branch 294 (VisitTree.leaf 287 [576]) (VisitTree.leaf 294 [602])))) (VisitTree.branch 323 (VisitTree.branch 319 (VisitTree.branch 312 (VisitTree.leaf 305 [594]) (VisitTree.leaf 312 [587])) (VisitTree.branch 320 (VisitTree.leaf 319 [586]) (VisitTree.leaf 320 [593]))) (VisitTree.branch 326 (VisitTree.branch 324 (VisitTree.leaf 323 [572]) (VisitTree.leaf 324 [594])) (VisitTree.branch 331 (VisitTree.leaf 326 [581]) (VisitTree.leaf 331 [585]))))) (VisitTree.branch 345 (VisitTree.branch 341 (VisitTree.branch 334 (VisitTree.branch 333 (VisitTree.leaf 332 [574]) (VisitTree.leaf 333 [600])) (VisitTree.branch 336 (VisitTree.leaf 334 [592]) (VisitTree.leaf 336 [586]))) (VisitTree.branch 343 (VisitTree.branch 342 (VisitTree.leaf 341 [587]) (VisitTree.leaf 342 [591])) (VisitTree.branch 344 (VisitTree.leaf 343 [576]) (VisitTree.leaf 344 [597])))) (VisitTree.branch 353 (VisitTree.branch 347 (VisitTree.branch 346 (VisitTree.leaf 345 [579]) (VisitTree.leaf 346 [596])) (VisitTree.branch 352 (VisitTree.leaf 347 [588]) (VisitTree.leaf 352 [590]))) (VisitTree.branch 358 (VisitTree.branch 357 (VisitTree.leaf 353 [575]) (VisitTree.leaf 357 [573])) (VisitTree.branch 362 (VisitTree.leaf 358 [572]) (VisitTree.leaf 362 [580])))))) (VisitTree.branch 451 (VisitTree.branch 386 (VisitTree.branch 373 (VisitTree.branch 369 (VisitTree.branch 365 (VisitTree.leaf 363 [574]) (VisitTree.leaf 365 [592])) (VisitTree.branch 371 (VisitTree.leaf 369 [582]) (VisitTree.leaf 371 [599]))) (VisitTree.branch 378 (VisitTree.branch 375 (VisitTree.leaf 373 [573]) (VisitTree.leaf 375 [571])) (VisitTree.branch 379 (VisitTree.leaf 378 [589]) (VisitTree.leaf 379 [580])))) (VisitTree.branch 409 (VisitTree.branch 400 (VisitTree.branch 398 (VisitTree.leaf 386 [589]) (VisitTree.leaf 398 [601])) (VisitTree.branch 407 (VisitTree.leaf 400 [579]) (VisitTree.leaf 407 [595]))) (VisitTree.branch 432 (VisitTree.branch 430 (VisitTree.leaf 409 [583]) (VisitTree.leaf 430 [577])) (VisitTree.branch 448 (VisitTree.leaf 432 [583]) (VisitTree.leaf 448 [596]))))) (VisitTree.branch 494 (VisitTree.branch 465 (VisitTree.branch 454 (VisitTree.branch 453 (VisitTree.leaf 451 [601]) (VisitTree.leaf 453 [585])) (VisitTree.branch 456 (VisitTree.leaf 454 [575]) (VisitTree.leaf 456 [584]))) (VisitTree.branch 491 (VisitTree.branch 487 (VisitTree.leaf 465 [577]) (VisitTree.leaf 487 [591])) (VisitTree.branch 492 (VisitTree.leaf 491 [597]) (VisitTree.leaf 492 [590])))) (VisitTree.branch 526 (VisitTree.branch 505 (VisitTree.branch 495 (VisitTree.leaf 494 [593]) (VisitTree.leaf 495 [588])) (VisitTree.branch 511 (VisitTree.leaf 505 [578]) (VisitTree.leaf 511 [577]))) (VisitTree.branch 600 (VisitTree.branch 589 (VisitTree.leaf 526 [599]) (VisitTree.leaf 589 [602])) (VisitTree.branch 659 (VisitTree.leaf 600 [600]) (VisitTree.leaf 659 [598]))))))))

def fastForwardChunkVisits095 (r : Nat) : List Nat :=
  forwardVisitTree095.lookup r

private theorem covered095 :
    visitsCovered forwardEventChunk095 forwardVisitTree095 = true := by
  decide +kernel

private theorem checked095 :
    visitsChecked forwardEventChunk095 forwardVisitTree095 = true := by
  decide +kernel

theorem eventVisits_forwardChunk095 (r : Nat) :
    eventVisits r forwardEventChunk095 = fastForwardChunkVisits095 r :=
  eventVisits_of_tree _ _ covered095 checked095 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk095

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 96. -/
def forwardVisitTree096 : VisitTree := (VisitTree.branch 236 (VisitTree.branch 191 (VisitTree.branch 66 (VisitTree.branch 24 (VisitTree.branch 12 (VisitTree.branch 7 (VisitTree.branch 4 (VisitTree.leaf 1 [634]) (VisitTree.leaf 4 [633])) (VisitTree.branch 8 (VisitTree.leaf 7 [628]) (VisitTree.leaf 8 [632]))) (VisitTree.branch 18 (VisitTree.branch 14 (VisitTree.leaf 12 [610]) (VisitTree.leaf 14 [625])) (VisitTree.branch 20 (VisitTree.leaf 18 [626]) (VisitTree.leaf 20 [631])))) (VisitTree.branch 40 (VisitTree.branch 33 (VisitTree.branch 29 (VisitTree.leaf 24 [613]) (VisitTree.leaf 29 [615])) (VisitTree.branch 37 (VisitTree.leaf 33 [614]) (VisitTree.leaf 37 [604]))) (VisitTree.branch 55 (VisitTree.branch 44 (VisitTree.leaf 40 [629]) (VisitTree.leaf 44 [607])) (VisitTree.branch 59 (VisitTree.leaf 55 [616]) (VisitTree.leaf 59 [627]))))) (VisitTree.branch 96 (VisitTree.branch 83 (VisitTree.branch 75 (VisitTree.branch 70 (VisitTree.leaf 66 [617]) (VisitTree.leaf 70 [609])) (VisitTree.branch 80 (VisitTree.leaf 75 [605]) (VisitTree.leaf 80 [621]))) (VisitTree.branch 88 (VisitTree.branch 85 (VisitTree.leaf 83 [611]) (VisitTree.leaf 85 [603])) (VisitTree.branch 90 (VisitTree.leaf 88 [624]) (VisitTree.leaf 90 [623])))) (VisitTree.branch 108 (VisitTree.branch 104 (VisitTree.branch 98 (VisitTree.leaf 96 [619]) (VisitTree.leaf 98 [620])) (VisitTree.branch 107 (VisitTree.leaf 104 [630]) (VisitTree.leaf 107 [606]))) (VisitTree.branch 189 (VisitTree.branch 110 (VisitTree.leaf 108 [618]) (VisitTree.leaf 110 [608])) (VisitTree.branch 190 (VisitTree.leaf 189 [603]) (VisitTree.leaf 190 [604])))))) (VisitTree.branch 207 (VisitTree.branch 199 (VisitTree.branch 195 (VisitTree.branch 193 (VisitTree.branch 192 (VisitTree.leaf 191 [605]) (VisitTree.leaf 192 [606])) (VisitTree.branch 194 (VisitTree.leaf 193 [607]) (VisitTree.leaf 194 [608]))) (VisitTree.branch 197 (VisitTree.branch 196 (VisitTree.leaf 195 [609]) (VisitTree.leaf 196 [610])) (VisitTree.branch 198 (VisitTree.leaf 197 [611]) (VisitTree.leaf 198 [612])))) (VisitTree.branch 203 (VisitTree.branch 201 (VisitTree.branch 200 (VisitTree.leaf 199 [613]) (VisitTree.leaf 200 [614])) (VisitTree.branch 202 (VisitTree.leaf 201 [615]) (VisitTree.leaf 202 [616]))) (VisitTree.branch 205 (VisitTree.branch 204 (VisitTree.leaf 203 [617]) (VisitTree.leaf 204 [618])) (VisitTree.branch 206 (VisitTree.leaf 205 [619]) (VisitTree.leaf 206 [620]))))) (VisitTree.branch 215 (VisitTree.branch 211 (VisitTree.branch 209 (VisitTree.branch 208 (VisitTree.leaf 207 [621]) (VisitTree.leaf 208 [622])) (VisitTree.branch 210 (VisitTree.leaf 209 [623]) (VisitTree.leaf 210 [624]))) (VisitTree.branch 213 (VisitTree.branch 212 (VisitTree.leaf 211 [625]) (VisitTree.leaf 212 [626])) (VisitTree.branch 214 (VisitTree.leaf 213 [627]) (VisitTree.leaf 214 [628])))) (VisitTree.branch 219 (VisitTree.branch 217 (VisitTree.branch 216 (VisitTree.leaf 215 [629]) (VisitTree.leaf 216 [630])) (VisitTree.branch 218 (VisitTree.leaf 217 [631]) (VisitTree.leaf 218 [632]))) (VisitTree.branch 226 (VisitTree.branch 220 (VisitTree.leaf 219 [633]) (VisitTree.leaf 220 [634])) (VisitTree.branch 227 (VisitTree.leaf 226 [634]) (VisitTree.leaf 227 [633]))))))) (VisitTree.branch 396 (VisitTree.branch 277 (VisitTree.branch 260 (VisitTree.branch 252 (VisitTree.branch 244 (VisitTree.branch 238 (VisitTree.leaf 236 [631]) (VisitTree.leaf 238 [630])) (VisitTree.branch 248 (VisitTree.leaf 244 [632]) (VisitTree.leaf 248 [610]))) (VisitTree.branch 258 (VisitTree.branch 255 (VisitTree.leaf 252 [616]) (VisitTree.leaf 255 [625])) (VisitTree.branch 259 (VisitTree.leaf 258 [618]) (VisitTree.leaf 259 [624])))) (VisitTree.branch 268 (VisitTree.branch 263 (VisitTree.branch 262 (VisitTree.leaf 260 [626]) (VisitTree.leaf 262 [618])) (VisitTree.branch 266 (VisitTree.leaf 263 [613]) (VisitTree.leaf 266 [625]))) (VisitTree.branch 275 (VisitTree.branch 274 (VisitTree.leaf 268 [627]) (VisitTree.leaf 274 [614])) (VisitTree.branch 276 (VisitTree.leaf 275 [626]) (VisitTree.leaf 276 [620]))))) (VisitTree.branch 298 (VisitTree.branch 284 (VisitTree.branch 282 (VisitTree.branch 280 (VisitTree.leaf 277 [628]) (VisitTree.leaf 280 [617])) (VisitTree.branch 283 (VisitTree.leaf 282 [603]) (VisitTree.leaf 283 [623]))) (VisitTree.branch 295 (VisitTree.branch 288 (VisitTree.leaf 284 [613]) (VisitTree.leaf 288 [606])) (VisitTree.branch 297 (VisitTree.leaf 295 [630]) (VisitTree.leaf 297 [612])))) (VisitTree.branch 316 (VisitTree.branch 304 (VisitTree.branch 302 (VisitTree.leaf 298 [605]) (VisitTree.leaf 302 [610])) (VisitTree.branch 307 (VisitTree.leaf 304 [604]) (VisitTree.leaf 307 [608]))) (VisitTree.branch 377 (VisitTree.branch 374 (VisitTree.leaf 316 [603]) (VisitTree.leaf 374 [604])) (VisitTree.branch 394 (VisitTree.leaf 377 [609]) (VisitTree.leaf 394 [611])))))) (VisitTree.branch 539 (VisitTree.branch 452 (VisitTree.branch 428 (VisitTree.branch 414 (VisitTree.branch 411 (VisitTree.leaf 396 [621]) (VisitTree.leaf 411 [629])) (VisitTree.branch 415 (VisitTree.leaf 414 [611]) (VisitTree.leaf 415 [631]))) (VisitTree.branch 435 (VisitTree.branch 429 (VisitTree.leaf 428 [623]) (VisitTree.leaf 429 [615])) (VisitTree.branch 443 (VisitTree.leaf 435 [620]) (VisitTree.leaf 443 [621])))) (VisitTree.branch 518 (VisitTree.branch 468 (VisitTree.branch 466 (VisitTree.leaf 452 [615]) (VisitTree.leaf 466 [612])) (VisitTree.branch 500 (VisitTree.leaf 468 [622]) (VisitTree.leaf 500 [607]))) (VisitTree.branch 521 (VisitTree.branch 519 (VisitTree.leaf 518 [622]) (VisitTree.leaf 519 [619])) (VisitTree.branch 537 (VisitTree.leaf 521 [614]) (VisitTree.leaf 537 [617]))))) (VisitTree.branch 588 (VisitTree.branch 562 (VisitTree.branch 556 (VisitTree.branch 542 (VisitTree.leaf 539 [616]) (VisitTree.leaf 542 [612])) (VisitTree.branch 557 (VisitTree.leaf 556 [627]) (VisitTree.leaf 557 [619]))) (VisitTree.branch 568 (VisitTree.branch 563 (VisitTree.leaf 562 [609]) (VisitTree.leaf 563 [605])) (VisitTree.branch 574 (VisitTree.leaf 568 [624]) (VisitTree.leaf 574 [622])))) (VisitTree.branch 619 (VisitTree.branch 611 (VisitTree.branch 595 (VisitTree.leaf 588 [608]) (VisitTree.leaf 595 [607])) (VisitTree.branch 618 (VisitTree.leaf 611 [634]) (VisitTree.leaf 618 [629]))) (VisitTree.branch 629 (VisitTree.branch 627 (VisitTree.leaf 619 [632]) (VisitTree.leaf 627 [633])) (VisitTree.branch 651 (VisitTree.leaf 629 [628]) (VisitTree.leaf 651 [606]))))))))

def fastForwardChunkVisits096 (r : Nat) : List Nat :=
  forwardVisitTree096.lookup r

private theorem covered096 :
    visitsCovered forwardEventChunk096 forwardVisitTree096 = true := by
  decide +kernel

private theorem checked096 :
    visitsChecked forwardEventChunk096 forwardVisitTree096 = true := by
  decide +kernel

theorem eventVisits_forwardChunk096 (r : Nat) :
    eventVisits r forwardEventChunk096 = fastForwardChunkVisits096 r :=
  eventVisits_of_tree _ _ covered096 checked096 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk096

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 97. -/
def forwardVisitTree097 : VisitTree := (VisitTree.branch 258 (VisitTree.branch 66 (VisitTree.branch 20 (VisitTree.branch 10 (VisitTree.branch 7 (VisitTree.branch 4 (VisitTree.leaf 1 [1]) (VisitTree.leaf 4 [1])) (VisitTree.branch 8 (VisitTree.leaf 7 [1]) (VisitTree.leaf 8 [1]))) (VisitTree.branch 14 (VisitTree.branch 12 (VisitTree.leaf 10 [635, 1]) (VisitTree.leaf 12 [1])) (VisitTree.branch 18 (VisitTree.leaf 14 [1]) (VisitTree.leaf 18 [1])))) (VisitTree.branch 40 (VisitTree.branch 29 (VisitTree.branch 24 (VisitTree.leaf 20 [1]) (VisitTree.leaf 24 [1])) (VisitTree.branch 33 (VisitTree.leaf 29 [1]) (VisitTree.leaf 33 [1]))) (VisitTree.branch 55 (VisitTree.branch 44 (VisitTree.leaf 40 [1]) (VisitTree.leaf 44 [1])) (VisitTree.branch 59 (VisitTree.leaf 55 [1]) (VisitTree.leaf 59 [1]))))) (VisitTree.branch 98 (VisitTree.branch 83 (VisitTree.branch 75 (VisitTree.branch 70 (VisitTree.leaf 66 [1]) (VisitTree.leaf 70 [1])) (VisitTree.branch 80 (VisitTree.leaf 75 [1]) (VisitTree.leaf 80 [1]))) (VisitTree.branch 90 (VisitTree.branch 88 (VisitTree.leaf 83 [1]) (VisitTree.leaf 88 [1])) (VisitTree.branch 96 (VisitTree.leaf 90 [1]) (VisitTree.leaf 96 [1])))) (VisitTree.branch 110 (VisitTree.branch 107 (VisitTree.branch 104 (VisitTree.leaf 98 [1]) (VisitTree.leaf 104 [1])) (VisitTree.branch 108 (VisitTree.leaf 107 [1]) (VisitTree.leaf 108 [1]))) (VisitTree.branch 236 (VisitTree.branch 221 (VisitTree.leaf 110 [1]) (VisitTree.leaf 221 [635])) (VisitTree.branch 238 (VisitTree.leaf 236 [1]) (VisitTree.leaf 238 [1])))))) (VisitTree.branch 594 (VisitTree.branch 466 (VisitTree.branch 298 (VisitTree.branch 268 (VisitTree.branch 260 (VisitTree.leaf 258 [1]) (VisitTree.leaf 260 [1])) (VisitTree.branch 274 (VisitTree.leaf 268 [1]) (VisitTree.leaf 274 [1]))) (VisitTree.branch 302 (VisitTree.branch 301 (VisitTree.leaf 298 [1]) (VisitTree.leaf 301 [1])) (VisitTree.branch 392 (VisitTree.leaf 302 [1]) (VisitTree.leaf 392 [1])))) (VisitTree.branch 544 (VisitTree.branch 536 (VisitTree.branch 468 (VisitTree.leaf 466 [1]) (VisitTree.leaf 468 [1])) (VisitTree.branch 543 (VisitTree.leaf 536 [1]) (VisitTree.leaf 543 [1]))) (VisitTree.branch 573 (VisitTree.branch 555 (VisitTree.leaf 544 [1]) (VisitTree.leaf 555 [1])) (VisitTree.branch 586 (VisitTree.leaf 573 [1]) (VisitTree.leaf 586 [1]))))) (VisitTree.branch 626 (VisitTree.branch 613 (VisitTree.branch 609 (VisitTree.branch 607 (VisitTree.leaf 594 [1]) (VisitTree.leaf 607 [1])) (VisitTree.branch 612 (VisitTree.leaf 609 [1]) (VisitTree.leaf 612 [1]))) (VisitTree.branch 620 (VisitTree.branch 616 (VisitTree.leaf 613 [1]) (VisitTree.leaf 616 [1])) (VisitTree.branch 624 (VisitTree.leaf 620 [1]) (VisitTree.leaf 624 [1])))) (VisitTree.branch 644 (VisitTree.branch 633 (VisitTree.branch 632 (VisitTree.leaf 626 [1]) (VisitTree.leaf 632 [1])) (VisitTree.branch 638 (VisitTree.leaf 633 [1]) (VisitTree.leaf 638 [1]))) (VisitTree.branch 647 (VisitTree.branch 646 (VisitTree.leaf 644 [635]) (VisitTree.leaf 646 [635])) (VisitTree.branch 650 (VisitTree.leaf 647 [1]) (VisitTree.branch 655 (VisitTree.leaf 650 [1]) (VisitTree.leaf 655 [1]))))))))

def fastForwardChunkVisits097 (r : Nat) : List Nat :=
  forwardVisitTree097.lookup r

private theorem covered097 :
    visitsCovered forwardEventChunk097 forwardVisitTree097 = true := by
  decide +kernel

private theorem checked097 :
    visitsChecked forwardEventChunk097 forwardVisitTree097 = true := by
  decide +kernel

theorem eventVisits_forwardChunk097 (r : Nat) :
    eventVisits r forwardEventChunk097 = fastForwardChunkVisits097 r :=
  eventVisits_of_tree _ _ covered097 checked097 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk097

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 98. -/
def forwardVisitTree098 : VisitTree := (VisitTree.branch 232 (VisitTree.branch 58 (VisitTree.branch 47 (VisitTree.branch 26 (VisitTree.branch 15 (VisitTree.branch 13 (VisitTree.leaf 3 [1]) (VisitTree.leaf 13 [1])) (VisitTree.branch 17 (VisitTree.leaf 15 [1]) (VisitTree.leaf 17 [1]))) (VisitTree.branch 37 (VisitTree.branch 30 (VisitTree.leaf 26 [1]) (VisitTree.leaf 30 [1])) (VisitTree.branch 46 (VisitTree.leaf 37 [1]) (VisitTree.leaf 46 [1])))) (VisitTree.branch 53 (VisitTree.branch 51 (VisitTree.branch 50 (VisitTree.leaf 47 [1]) (VisitTree.leaf 50 [1])) (VisitTree.branch 52 (VisitTree.leaf 51 [1]) (VisitTree.leaf 52 [1]))) (VisitTree.branch 56 (VisitTree.branch 54 (VisitTree.leaf 53 [1]) (VisitTree.leaf 54 [1])) (VisitTree.branch 57 (VisitTree.leaf 56 [1]) (VisitTree.leaf 57 [1]))))) (VisitTree.branch 71 (VisitTree.branch 64 (VisitTree.branch 61 (VisitTree.branch 60 (VisitTree.leaf 58 [1]) (VisitTree.leaf 60 [1])) (VisitTree.branch 63 (VisitTree.leaf 61 [1]) (VisitTree.leaf 63 [1]))) (VisitTree.branch 67 (VisitTree.branch 65 (VisitTree.leaf 64 [1]) (VisitTree.leaf 65 [1])) (VisitTree.branch 68 (VisitTree.leaf 67 [1]) (VisitTree.leaf 68 [1])))) (VisitTree.branch 85 (VisitTree.branch 82 (VisitTree.branch 74 (VisitTree.leaf 71 [1]) (VisitTree.leaf 74 [1])) (VisitTree.branch 84 (VisitTree.leaf 82 [1]) (VisitTree.leaf 84 [1]))) (VisitTree.branch 105 (VisitTree.branch 89 (VisitTree.leaf 85 [1]) (VisitTree.leaf 89 [1])) (VisitTree.branch 225 (VisitTree.leaf 105 [1]) (VisitTree.leaf 225 [1])))))) (VisitTree.branch 404 (VisitTree.branch 334 (VisitTree.branch 312 (VisitTree.branch 256 (VisitTree.branch 251 (VisitTree.leaf 232 [1]) (VisitTree.leaf 251 [1])) (VisitTree.branch 304 (VisitTree.leaf 256 [1]) (VisitTree.leaf 304 [1]))) (VisitTree.branch 324 (VisitTree.branch 323 (VisitTree.leaf 312 [1]) (VisitTree.leaf 323 [1])) (VisitTree.branch 326 (VisitTree.leaf 324 [1]) (VisitTree.leaf 326 [1])))) (VisitTree.branch 347 (VisitTree.branch 342 (VisitTree.branch 336 (VisitTree.leaf 334 [1]) (VisitTree.leaf 336 [1])) (VisitTree.branch 346 (VisitTree.leaf 342 [1]) (VisitTree.leaf 346 [1]))) (VisitTree.branch 378 (VisitTree.branch 362 (VisitTree.leaf 347 [1]) (VisitTree.leaf 362 [1])) (VisitTree.branch 379 (VisitTree.leaf 378 [1]) (VisitTree.leaf 379 [1]))))) (VisitTree.branch 494 (VisitTree.branch 456 (VisitTree.branch 453 (VisitTree.branch 432 (VisitTree.leaf 404 [1]) (VisitTree.leaf 432 [1])) (VisitTree.branch 454 (VisitTree.leaf 453 [1]) (VisitTree.leaf 454 [1]))) (VisitTree.branch 491 (VisitTree.branch 465 (VisitTree.leaf 456 [1]) (VisitTree.leaf 465 [1])) (VisitTree.branch 492 (VisitTree.leaf 491 [1]) (VisitTree.leaf 492 [1])))) (VisitTree.branch 565 (VisitTree.branch 505 (VisitTree.branch 500 (VisitTree.leaf 494 [1]) (VisitTree.leaf 500 [1])) (VisitTree.branch 511 (VisitTree.leaf 505 [1]) (VisitTree.leaf 511 [1]))) (VisitTree.branch 601 (VisitTree.branch 581 (VisitTree.leaf 565 [1]) (VisitTree.leaf 581 [1])) (VisitTree.branch 658 (VisitTree.leaf 601 [1]) (VisitTree.leaf 658 [1])))))))

def fastForwardChunkVisits098 (r : Nat) : List Nat :=
  forwardVisitTree098.lookup r

private theorem covered098 :
    visitsCovered forwardEventChunk098 forwardVisitTree098 = true := by
  decide +kernel

private theorem checked098 :
    visitsChecked forwardEventChunk098 forwardVisitTree098 = true := by
  decide +kernel

theorem eventVisits_forwardChunk098 (r : Nat) :
    eventVisits r forwardEventChunk098 = fastForwardChunkVisits098 r :=
  eventVisits_of_tree _ _ covered098 checked098 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk098

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 99. -/
def forwardVisitTree099 : VisitTree := (VisitTree.branch 253 (VisitTree.branch 77 (VisitTree.branch 38 (VisitTree.branch 28 (VisitTree.branch 23 (VisitTree.branch 16 (VisitTree.leaf 11 [1]) (VisitTree.leaf 16 [1])) (VisitTree.branch 27 (VisitTree.leaf 23 [1]) (VisitTree.leaf 27 [1]))) (VisitTree.branch 35 (VisitTree.branch 32 (VisitTree.leaf 28 [1]) (VisitTree.leaf 32 [1])) (VisitTree.branch 36 (VisitTree.leaf 35 [1]) (VisitTree.leaf 36 [1])))) (VisitTree.branch 45 (VisitTree.branch 42 (VisitTree.branch 41 (VisitTree.leaf 38 [1]) (VisitTree.leaf 41 [1])) (VisitTree.branch 43 (VisitTree.leaf 42 [1]) (VisitTree.leaf 43 [1]))) (VisitTree.branch 72 (VisitTree.branch 49 (VisitTree.leaf 45 [1]) (VisitTree.leaf 49 [1])) (VisitTree.branch 76 (VisitTree.leaf 72 [1]) (VisitTree.leaf 76 [1]))))) (VisitTree.branch 94 (VisitTree.branch 86 (VisitTree.branch 79 (VisitTree.branch 78 (VisitTree.leaf 77 [1]) (VisitTree.leaf 78 [1])) (VisitTree.branch 81 (VisitTree.leaf 79 [1]) (VisitTree.leaf 81 [1]))) (VisitTree.branch 91 (VisitTree.branch 87 (VisitTree.leaf 86 [1]) (VisitTree.leaf 87 [1])) (VisitTree.branch 92 (VisitTree.leaf 91 [1]) (VisitTree.leaf 92 [1])))) (VisitTree.branch 101 (VisitTree.branch 97 (VisitTree.branch 95 (VisitTree.leaf 94 [1]) (VisitTree.leaf 95 [1])) (VisitTree.branch 100 (VisitTree.leaf 97 [1]) (VisitTree.leaf 100 [1]))) (VisitTree.branch 103 (VisitTree.branch 102 (VisitTree.leaf 101 [1]) (VisitTree.leaf 102 [1])) (VisitTree.branch 109 (VisitTree.leaf 103 [1]) (VisitTree.leaf 109 [1])))))) (VisitTree.branch 439 (VisitTree.branch 389 (VisitTree.branch 282 (VisitTree.branch 262 (VisitTree.branch 255 (VisitTree.leaf 253 [1]) (VisitTree.leaf 255 [1])) (VisitTree.branch 275 (VisitTree.leaf 262 [1]) (VisitTree.leaf 275 [1]))) (VisitTree.branch 373 (VisitTree.branch 345 (VisitTree.leaf 282 [1]) (VisitTree.leaf 345 [1])) (VisitTree.branch 374 (VisitTree.leaf 373 [1]) (VisitTree.leaf 374 [1])))) (VisitTree.branch 419 (VisitTree.branch 405 (VisitTree.branch 401 (VisitTree.leaf 389 [1]) (VisitTree.leaf 401 [1])) (VisitTree.branch 414 (VisitTree.leaf 405 [1]) (VisitTree.leaf 414 [1]))) (VisitTree.branch 427 (VisitTree.branch 425 (VisitTree.leaf 419 [1]) (VisitTree.leaf 425 [1])) (VisitTree.branch 437 (VisitTree.leaf 427 [1]) (VisitTree.leaf 437 [1]))))) (VisitTree.branch 563 (VisitTree.branch 526 (VisitTree.branch 518 (VisitTree.branch 502 (VisitTree.leaf 439 [1]) (VisitTree.leaf 502 [1])) (VisitTree.branch 521 (VisitTree.leaf 518 [1]) (VisitTree.leaf 521 [1]))) (VisitTree.branch 537 (VisitTree.branch 527 (VisitTree.leaf 526 [1]) (VisitTree.leaf 527 [1])) (VisitTree.branch 556 (VisitTree.leaf 537 [1]) (VisitTree.leaf 556 [1])))) (VisitTree.branch 589 (VisitTree.branch 578 (VisitTree.branch 568 (VisitTree.leaf 563 [1]) (VisitTree.leaf 568 [1])) (VisitTree.branch 588 (VisitTree.leaf 578 [1]) (VisitTree.leaf 588 [1]))) (VisitTree.branch 628 (VisitTree.branch 600 (VisitTree.leaf 589 [1]) (VisitTree.leaf 600 [1])) (VisitTree.branch 654 (VisitTree.leaf 628 [1]) (VisitTree.leaf 654 [1])))))))

def fastForwardChunkVisits099 (r : Nat) : List Nat :=
  forwardVisitTree099.lookup r

private theorem covered099 :
    visitsCovered forwardEventChunk099 forwardVisitTree099 = true := by
  decide +kernel

private theorem checked099 :
    visitsChecked forwardEventChunk099 forwardVisitTree099 = true := by
  decide +kernel

theorem eventVisits_forwardChunk099 (r : Nat) :
    eventVisits r forwardEventChunk099 = fastForwardChunkVisits099 r :=
  eventVisits_of_tree _ _ covered099 checked099 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk099


