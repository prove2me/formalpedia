-- Prove2me | Definitions.Def_CSL_Generated_MemoryAccess_Group04
-- name    : CSL_Generated_MemoryAccess_Group04
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T13:29:31.039812+00:00
-- url     : https://prove2.me/theorems/a1827f08-0fbe-46b8-94f5-26f56b201c41
-- title:
--   Coded sorting library: Generated / MemoryAccess / Group04
-- statement:
--   Module `CodedSorting.Generated.MemoryAccess.Group04` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Generated.MemoryAccess.Group04

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Circuit_MemoryAccess_PhysicalFrameEventChunkData
import Definitions.Def_CSL_Generated_MemoryAccess_Base

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 68. -/
def forwardVisitTree068 : VisitTree := (VisitTree.branch 387 (VisitTree.branch 331 (VisitTree.branch 280 (VisitTree.branch 241 (VisitTree.leaf 233 [515]) (VisitTree.leaf 241 [516])) (VisitTree.branch 296 (VisitTree.leaf 280 [421]) (VisitTree.branch 328 (VisitTree.leaf 296 [517]) (VisitTree.leaf 328 [514])))) (VisitTree.branch 341 (VisitTree.branch 340 (VisitTree.leaf 331 [431]) (VisitTree.leaf 340 [515])) (VisitTree.branch 368 (VisitTree.leaf 341 [350]) (VisitTree.branch 385 (VisitTree.leaf 368 [518]) (VisitTree.leaf 385 [514]))))) (VisitTree.branch 479 (VisitTree.branch 476 (VisitTree.branch 413 (VisitTree.leaf 387 [516]) (VisitTree.leaf 413 [517])) (VisitTree.branch 477 (VisitTree.leaf 476 [431, 514]) (VisitTree.branch 478 (VisitTree.leaf 477 [350, 515]) (VisitTree.leaf 478 [359, 516])))) (VisitTree.branch 495 (VisitTree.branch 480 (VisitTree.leaf 479 [388, 517]) (VisitTree.leaf 480 [421, 518])) (VisitTree.branch 538 (VisitTree.leaf 495 [359]) (VisitTree.branch 561 (VisitTree.leaf 538 [518]) (VisitTree.leaf 561 [388]))))))

def fastForwardChunkVisits068 (r : Nat) : List Nat :=
  forwardVisitTree068.lookup r

private theorem covered068 :
    visitsCovered forwardEventChunk068 forwardVisitTree068 = true := by
  decide +kernel

private theorem checked068 :
    visitsChecked forwardEventChunk068 forwardVisitTree068 = true := by
  decide +kernel

theorem eventVisits_forwardChunk068 (r : Nat) :
    eventVisits r forwardEventChunk068 = fastForwardChunkVisits068 r :=
  eventVisits_of_tree _ _ covered068 checked068 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk068

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 69. -/
def forwardVisitTree069 : VisitTree := (VisitTree.branch 661 (VisitTree.branch 476 (VisitTree.branch 474 (VisitTree.branch 473 (VisitTree.leaf 472 [510]) (VisitTree.leaf 473 [511])) (VisitTree.branch 475 (VisitTree.leaf 474 [512]) (VisitTree.leaf 475 [513]))) (VisitTree.branch 478 (VisitTree.branch 477 (VisitTree.leaf 476 [514]) (VisitTree.leaf 477 [515])) (VisitTree.branch 479 (VisitTree.leaf 478 [516]) (VisitTree.branch 480 (VisitTree.leaf 479 [517]) (VisitTree.leaf 480 [518]))))) (VisitTree.branch 665 (VisitTree.branch 663 (VisitTree.branch 662 (VisitTree.leaf 661 [510]) (VisitTree.leaf 662 [511])) (VisitTree.branch 664 (VisitTree.leaf 663 [512]) (VisitTree.leaf 664 [513]))) (VisitTree.branch 667 (VisitTree.branch 666 (VisitTree.leaf 665 [514]) (VisitTree.leaf 666 [515])) (VisitTree.branch 668 (VisitTree.leaf 667 [516]) (VisitTree.branch 669 (VisitTree.leaf 668 [517]) (VisitTree.leaf 669 [518]))))))

def fastForwardChunkVisits069 (r : Nat) : List Nat :=
  forwardVisitTree069.lookup r

private theorem covered069 :
    visitsCovered forwardEventChunk069 forwardVisitTree069 = true := by
  decide +kernel

private theorem checked069 :
    visitsChecked forwardEventChunk069 forwardVisitTree069 = true := by
  decide +kernel

theorem eventVisits_forwardChunk069 (r : Nat) :
    eventVisits r forwardEventChunk069 = fastForwardChunkVisits069 r :=
  eventVisits_of_tree _ _ covered069 checked069 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk069

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 70. -/
def forwardVisitTree070 : VisitTree := (VisitTree.branch 126 (VisitTree.branch 118 (VisitTree.branch 114 (VisitTree.branch 112 (VisitTree.leaf 111 [0]) (VisitTree.branch 113 (VisitTree.leaf 112 [0]) (VisitTree.leaf 113 [0]))) (VisitTree.branch 116 (VisitTree.branch 115 (VisitTree.leaf 114 [0]) (VisitTree.leaf 115 [0])) (VisitTree.branch 117 (VisitTree.leaf 116 [0]) (VisitTree.leaf 117 [0])))) (VisitTree.branch 122 (VisitTree.branch 120 (VisitTree.branch 119 (VisitTree.leaf 118 [0]) (VisitTree.leaf 119 [0])) (VisitTree.branch 121 (VisitTree.leaf 120 [0]) (VisitTree.leaf 121 [0]))) (VisitTree.branch 124 (VisitTree.branch 123 (VisitTree.leaf 122 [0]) (VisitTree.leaf 123 [0])) (VisitTree.branch 125 (VisitTree.leaf 124 [0]) (VisitTree.leaf 125 [0]))))) (VisitTree.branch 662 (VisitTree.branch 130 (VisitTree.branch 128 (VisitTree.branch 127 (VisitTree.leaf 126 [0]) (VisitTree.leaf 127 [0])) (VisitTree.branch 129 (VisitTree.leaf 128 [0]) (VisitTree.leaf 129 [0]))) (VisitTree.branch 132 (VisitTree.branch 131 (VisitTree.leaf 130 [0]) (VisitTree.leaf 131 [0])) (VisitTree.branch 661 (VisitTree.leaf 132 [0]) (VisitTree.leaf 661 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])))) (VisitTree.branch 666 (VisitTree.branch 664 (VisitTree.branch 663 (VisitTree.leaf 662 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 663 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) (VisitTree.branch 665 (VisitTree.leaf 664 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 665 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) (VisitTree.branch 668 (VisitTree.branch 667 (VisitTree.leaf 666 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 667 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) (VisitTree.branch 669 (VisitTree.leaf 668 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 669 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))))))

def fastForwardChunkVisits070 (r : Nat) : List Nat :=
  forwardVisitTree070.lookup r

private theorem covered070 :
    visitsCovered forwardEventChunk070 forwardVisitTree070 = true := by
  decide +kernel

private theorem checked070 :
    visitsChecked forwardEventChunk070 forwardVisitTree070 = true := by
  decide +kernel

theorem eventVisits_forwardChunk070 (r : Nat) :
    eventVisits r forwardEventChunk070 = fastForwardChunkVisits070 r :=
  eventVisits_of_tree _ _ covered070 checked070 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk070

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 71. -/
def forwardVisitTree071 : VisitTree := (VisitTree.branch 153 (VisitTree.branch 143 (VisitTree.branch 138 (VisitTree.branch 135 (VisitTree.branch 134 (VisitTree.leaf 133 [0]) (VisitTree.leaf 134 [0])) (VisitTree.branch 136 (VisitTree.leaf 135 [0]) (VisitTree.branch 137 (VisitTree.leaf 136 [0]) (VisitTree.leaf 137 [0])))) (VisitTree.branch 140 (VisitTree.branch 139 (VisitTree.leaf 138 [0]) (VisitTree.leaf 139 [0])) (VisitTree.branch 141 (VisitTree.leaf 140 [0]) (VisitTree.branch 142 (VisitTree.leaf 141 [0]) (VisitTree.leaf 142 [0]))))) (VisitTree.branch 148 (VisitTree.branch 145 (VisitTree.branch 144 (VisitTree.leaf 143 [0]) (VisitTree.leaf 144 [0])) (VisitTree.branch 146 (VisitTree.leaf 145 [0]) (VisitTree.branch 147 (VisitTree.leaf 146 [0]) (VisitTree.leaf 147 [0])))) (VisitTree.branch 150 (VisitTree.branch 149 (VisitTree.leaf 148 [0]) (VisitTree.leaf 149 [0])) (VisitTree.branch 151 (VisitTree.leaf 150 [0]) (VisitTree.branch 152 (VisitTree.leaf 151 [0]) (VisitTree.leaf 152 [0])))))) (VisitTree.branch 163 (VisitTree.branch 158 (VisitTree.branch 155 (VisitTree.branch 154 (VisitTree.leaf 153 [0]) (VisitTree.leaf 154 [0])) (VisitTree.branch 156 (VisitTree.leaf 155 [0]) (VisitTree.branch 157 (VisitTree.leaf 156 [0]) (VisitTree.leaf 157 [0])))) (VisitTree.branch 160 (VisitTree.branch 159 (VisitTree.leaf 158 [0]) (VisitTree.leaf 159 [0])) (VisitTree.branch 161 (VisitTree.leaf 160 [0]) (VisitTree.branch 162 (VisitTree.leaf 161 [0]) (VisitTree.leaf 162 [0]))))) (VisitTree.branch 664 (VisitTree.branch 661 (VisitTree.branch 164 (VisitTree.leaf 163 [0]) (VisitTree.leaf 164 [0])) (VisitTree.branch 662 (VisitTree.leaf 661 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 663 (VisitTree.leaf 662 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 663 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])))) (VisitTree.branch 667 (VisitTree.branch 665 (VisitTree.leaf 664 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 666 (VisitTree.leaf 665 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 666 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) (VisitTree.branch 668 (VisitTree.leaf 667 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 669 (VisitTree.leaf 668 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 669 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])))))))

def fastForwardChunkVisits071 (r : Nat) : List Nat :=
  forwardVisitTree071.lookup r

private theorem covered071 :
    visitsCovered forwardEventChunk071 forwardVisitTree071 = true := by
  decide +kernel

private theorem checked071 :
    visitsChecked forwardEventChunk071 forwardVisitTree071 = true := by
  decide +kernel

theorem eventVisits_forwardChunk071 (r : Nat) :
    eventVisits r forwardEventChunk071 = fastForwardChunkVisits071 r :=
  eventVisits_of_tree _ _ covered071 checked071 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk071

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 72. -/
def forwardVisitTree072 : VisitTree := (VisitTree.branch 185 (VisitTree.branch 175 (VisitTree.branch 170 (VisitTree.branch 167 (VisitTree.branch 166 (VisitTree.leaf 165 [0]) (VisitTree.leaf 166 [0])) (VisitTree.branch 168 (VisitTree.leaf 167 [0]) (VisitTree.branch 169 (VisitTree.leaf 168 [0]) (VisitTree.leaf 169 [0])))) (VisitTree.branch 172 (VisitTree.branch 171 (VisitTree.leaf 170 [0]) (VisitTree.leaf 171 [0])) (VisitTree.branch 173 (VisitTree.leaf 172 [0]) (VisitTree.branch 174 (VisitTree.leaf 173 [0]) (VisitTree.leaf 174 [0]))))) (VisitTree.branch 180 (VisitTree.branch 177 (VisitTree.branch 176 (VisitTree.leaf 175 [0]) (VisitTree.leaf 176 [0])) (VisitTree.branch 178 (VisitTree.leaf 177 [0]) (VisitTree.branch 179 (VisitTree.leaf 178 [0]) (VisitTree.leaf 179 [0])))) (VisitTree.branch 182 (VisitTree.branch 181 (VisitTree.leaf 180 [0]) (VisitTree.leaf 181 [0])) (VisitTree.branch 183 (VisitTree.leaf 182 [0]) (VisitTree.branch 184 (VisitTree.leaf 183 [0]) (VisitTree.leaf 184 [0])))))) (VisitTree.branch 195 (VisitTree.branch 190 (VisitTree.branch 187 (VisitTree.branch 186 (VisitTree.leaf 185 [0]) (VisitTree.leaf 186 [0])) (VisitTree.branch 188 (VisitTree.leaf 187 [0]) (VisitTree.branch 189 (VisitTree.leaf 188 [0]) (VisitTree.leaf 189 [0])))) (VisitTree.branch 192 (VisitTree.branch 191 (VisitTree.leaf 190 [0]) (VisitTree.leaf 191 [0])) (VisitTree.branch 193 (VisitTree.leaf 192 [0]) (VisitTree.branch 194 (VisitTree.leaf 193 [0]) (VisitTree.leaf 194 [0]))))) (VisitTree.branch 664 (VisitTree.branch 661 (VisitTree.branch 196 (VisitTree.leaf 195 [0]) (VisitTree.leaf 196 [0])) (VisitTree.branch 662 (VisitTree.leaf 661 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 663 (VisitTree.leaf 662 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 663 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])))) (VisitTree.branch 667 (VisitTree.branch 665 (VisitTree.leaf 664 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 666 (VisitTree.leaf 665 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 666 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) (VisitTree.branch 668 (VisitTree.leaf 667 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 669 (VisitTree.leaf 668 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 669 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])))))))

def fastForwardChunkVisits072 (r : Nat) : List Nat :=
  forwardVisitTree072.lookup r

private theorem covered072 :
    visitsCovered forwardEventChunk072 forwardVisitTree072 = true := by
  decide +kernel

private theorem checked072 :
    visitsChecked forwardEventChunk072 forwardVisitTree072 = true := by
  decide +kernel

theorem eventVisits_forwardChunk072 (r : Nat) :
    eventVisits r forwardEventChunk072 = fastForwardChunkVisits072 r :=
  eventVisits_of_tree _ _ covered072 checked072 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk072

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 73. -/
def forwardVisitTree073 : VisitTree := (VisitTree.branch 214 (VisitTree.branch 205 (VisitTree.branch 201 (VisitTree.branch 199 (VisitTree.branch 198 (VisitTree.leaf 197 [0]) (VisitTree.leaf 198 [0])) (VisitTree.branch 200 (VisitTree.leaf 199 [0]) (VisitTree.leaf 200 [0]))) (VisitTree.branch 203 (VisitTree.branch 202 (VisitTree.leaf 201 [0]) (VisitTree.leaf 202 [0])) (VisitTree.branch 204 (VisitTree.leaf 203 [0]) (VisitTree.leaf 204 [0])))) (VisitTree.branch 209 (VisitTree.branch 207 (VisitTree.branch 206 (VisitTree.leaf 205 [0]) (VisitTree.leaf 206 [0])) (VisitTree.branch 208 (VisitTree.leaf 207 [0]) (VisitTree.leaf 208 [0]))) (VisitTree.branch 211 (VisitTree.branch 210 (VisitTree.leaf 209 [0]) (VisitTree.leaf 210 [0])) (VisitTree.branch 212 (VisitTree.leaf 211 [0]) (VisitTree.branch 213 (VisitTree.leaf 212 [0]) (VisitTree.leaf 213 [0])))))) (VisitTree.branch 661 (VisitTree.branch 218 (VisitTree.branch 216 (VisitTree.branch 215 (VisitTree.leaf 214 [0]) (VisitTree.leaf 215 [0])) (VisitTree.branch 217 (VisitTree.leaf 216 [0]) (VisitTree.leaf 217 [0]))) (VisitTree.branch 220 (VisitTree.branch 219 (VisitTree.leaf 218 [0]) (VisitTree.leaf 219 [0])) (VisitTree.branch 221 (VisitTree.leaf 220 [0]) (VisitTree.leaf 221 [0])))) (VisitTree.branch 665 (VisitTree.branch 663 (VisitTree.branch 662 (VisitTree.leaf 661 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 662 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) (VisitTree.branch 664 (VisitTree.leaf 663 [0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 664 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) (VisitTree.branch 667 (VisitTree.branch 666 (VisitTree.leaf 665 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 666 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) (VisitTree.branch 668 (VisitTree.leaf 667 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 669 (VisitTree.leaf 668 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 669 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])))))))

def fastForwardChunkVisits073 (r : Nat) : List Nat :=
  forwardVisitTree073.lookup r

private theorem covered073 :
    visitsCovered forwardEventChunk073 forwardVisitTree073 = true := by
  decide +kernel

private theorem checked073 :
    visitsChecked forwardEventChunk073 forwardVisitTree073 = true := by
  decide +kernel

theorem eventVisits_forwardChunk073 (r : Nat) :
    eventVisits r forwardEventChunk073 = fastForwardChunkVisits073 r :=
  eventVisits_of_tree _ _ covered073 checked073 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk073

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 74. -/
def forwardVisitTree074 : VisitTree := (VisitTree.branch 111 (VisitTree.branch 103 (VisitTree.branch 5 (VisitTree.leaf 3 [127]) (VisitTree.branch 9 (VisitTree.leaf 5 [114]) (VisitTree.leaf 9 [11]))) (VisitTree.branch 108 (VisitTree.branch 106 (VisitTree.leaf 103 [233]) (VisitTree.leaf 106 [217])) (VisitTree.branch 109 (VisitTree.leaf 108 [214]) (VisitTree.leaf 109 [235])))) (VisitTree.branch 115 (VisitTree.branch 112 (VisitTree.leaf 111 [127]) (VisitTree.branch 113 (VisitTree.leaf 112 [217]) (VisitTree.leaf 113 [233]))) (VisitTree.branch 117 (VisitTree.branch 116 (VisitTree.leaf 115 [235]) (VisitTree.leaf 116 [11])) (VisitTree.branch 118 (VisitTree.leaf 117 [114]) (VisitTree.leaf 118 [214])))))

def fastForwardChunkVisits074 (r : Nat) : List Nat :=
  forwardVisitTree074.lookup r

private theorem covered074 :
    visitsCovered forwardEventChunk074 forwardVisitTree074 = true := by
  decide +kernel

private theorem checked074 :
    visitsChecked forwardEventChunk074 forwardVisitTree074 = true := by
  decide +kernel

theorem eventVisits_forwardChunk074 (r : Nat) :
    eventVisits r forwardEventChunk074 = fastForwardChunkVisits074 r :=
  eventVisits_of_tree _ _ covered074 checked074 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk074

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 75. -/
def forwardVisitTree075 : VisitTree := (VisitTree.branch 119 (VisitTree.branch 81 (VisitTree.branch 38 (VisitTree.branch 25 (VisitTree.branch 12 (VisitTree.branch 8 (VisitTree.leaf 0 [2]) (VisitTree.leaf 8 [249])) (VisitTree.branch 21 (VisitTree.leaf 12 [252]) (VisitTree.leaf 21 [165]))) (VisitTree.branch 29 (VisitTree.branch 26 (VisitTree.leaf 25 [226]) (VisitTree.leaf 26 [168])) (VisitTree.branch 32 (VisitTree.leaf 29 [222]) (VisitTree.leaf 32 [202])))) (VisitTree.branch 75 (VisitTree.branch 45 (VisitTree.branch 41 (VisitTree.leaf 38 [188]) (VisitTree.leaf 41 [143])) (VisitTree.branch 74 (VisitTree.leaf 45 [263]) (VisitTree.leaf 74 [160]))) (VisitTree.branch 79 (VisitTree.branch 77 (VisitTree.leaf 75 [145]) (VisitTree.leaf 77 [186])) (VisitTree.branch 80 (VisitTree.leaf 79 [211]) (VisitTree.leaf 80 [173]))))) (VisitTree.branch 93 (VisitTree.branch 89 (VisitTree.branch 86 (VisitTree.branch 85 (VisitTree.leaf 81 [257]) (VisitTree.leaf 85 [205])) (VisitTree.branch 88 (VisitTree.leaf 86 [259]) (VisitTree.leaf 88 [247]))) (VisitTree.branch 91 (VisitTree.branch 90 (VisitTree.leaf 89 [155]) (VisitTree.leaf 90 [239])) (VisitTree.branch 92 (VisitTree.leaf 91 [135]) (VisitTree.leaf 92 [184])))) (VisitTree.branch 98 (VisitTree.branch 96 (VisitTree.branch 95 (VisitTree.leaf 93 [246]) (VisitTree.leaf 95 [241])) (VisitTree.branch 97 (VisitTree.leaf 96 [139]) (VisitTree.leaf 97 [154]))) (VisitTree.branch 104 (VisitTree.branch 101 (VisitTree.leaf 98 [229]) (VisitTree.leaf 101 [223])) (VisitTree.branch 107 (VisitTree.leaf 104 [199]) (VisitTree.leaf 107 [198])))))) (VisitTree.branch 137 (VisitTree.branch 128 (VisitTree.branch 124 (VisitTree.branch 122 (VisitTree.branch 121 (VisitTree.leaf 119 [252]) (VisitTree.leaf 121 [198])) (VisitTree.branch 123 (VisitTree.leaf 122 [2]) (VisitTree.leaf 123 [249]))) (VisitTree.branch 126 (VisitTree.branch 125 (VisitTree.leaf 124 [199]) (VisitTree.leaf 125 [239])) (VisitTree.branch 127 (VisitTree.leaf 126 [139]) (VisitTree.leaf 127 [246])))) (VisitTree.branch 132 (VisitTree.branch 130 (VisitTree.branch 129 (VisitTree.leaf 128 [184]) (VisitTree.leaf 129 [247])) (VisitTree.branch 131 (VisitTree.leaf 130 [155]) (VisitTree.leaf 131 [241]))) (VisitTree.branch 135 (VisitTree.branch 134 (VisitTree.leaf 132 [168]) (VisitTree.leaf 134 [135])) (VisitTree.branch 136 (VisitTree.leaf 135 [222]) (VisitTree.leaf 136 [229]))))) (VisitTree.branch 145 (VisitTree.branch 141 (VisitTree.branch 139 (VisitTree.branch 138 (VisitTree.leaf 137 [165]) (VisitTree.leaf 138 [154])) (VisitTree.branch 140 (VisitTree.leaf 139 [226]) (VisitTree.leaf 140 [223]))) (VisitTree.branch 143 (VisitTree.branch 142 (VisitTree.leaf 141 [143]) (VisitTree.leaf 142 [257])) (VisitTree.branch 144 (VisitTree.leaf 143 [205]) (VisitTree.leaf 144 [188])))) (VisitTree.branch 149 (VisitTree.branch 147 (VisitTree.branch 146 (VisitTree.leaf 145 [202]) (VisitTree.leaf 146 [160])) (VisitTree.branch 148 (VisitTree.leaf 147 [173]) (VisitTree.leaf 148 [259]))) (VisitTree.branch 151 (VisitTree.branch 150 (VisitTree.leaf 149 [186]) (VisitTree.leaf 150 [211])) (VisitTree.branch 152 (VisitTree.leaf 151 [263]) (VisitTree.leaf 152 [145])))))))

def fastForwardChunkVisits075 (r : Nat) : List Nat :=
  forwardVisitTree075.lookup r

private theorem covered075 :
    visitsCovered forwardEventChunk075 forwardVisitTree075 = true := by
  decide +kernel

private theorem checked075 :
    visitsChecked forwardEventChunk075 forwardVisitTree075 = true := by
  decide +kernel

theorem eventVisits_forwardChunk075 (r : Nat) :
    eventVisits r forwardEventChunk075 = fastForwardChunkVisits075 r :=
  eventVisits_of_tree _ _ covered075 checked075 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk075

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 76. -/
def forwardVisitTree076 : VisitTree := (VisitTree.branch 153 (VisitTree.branch 59 (VisitTree.branch 49 (VisitTree.branch 42 (VisitTree.branch 39 (VisitTree.branch 36 (VisitTree.leaf 35 [159]) (VisitTree.leaf 36 [172])) (VisitTree.branch 40 (VisitTree.leaf 39 [207]) (VisitTree.leaf 40 [260]))) (VisitTree.branch 47 (VisitTree.branch 46 (VisitTree.leaf 42 [206]) (VisitTree.leaf 46 [48])) (VisitTree.branch 48 (VisitTree.leaf 47 [121]) (VisitTree.leaf 48 [119])))) (VisitTree.branch 53 (VisitTree.branch 51 (VisitTree.branch 50 (VisitTree.leaf 49 [146]) (VisitTree.leaf 50 [52])) (VisitTree.branch 52 (VisitTree.leaf 51 [178]) (VisitTree.leaf 52 [120]))) (VisitTree.branch 55 (VisitTree.branch 54 (VisitTree.leaf 53 [149]) (VisitTree.leaf 54 [56])) (VisitTree.branch 58 (VisitTree.leaf 55 [179]) (VisitTree.leaf 58 [124]))))) (VisitTree.branch 70 (VisitTree.branch 63 (VisitTree.branch 61 (VisitTree.branch 60 (VisitTree.leaf 59 [147]) (VisitTree.leaf 60 [62])) (VisitTree.branch 62 (VisitTree.leaf 61 [63]) (VisitTree.leaf 62 [129]))) (VisitTree.branch 65 (VisitTree.branch 64 (VisitTree.leaf 63 [131]) (VisitTree.leaf 64 [181])) (VisitTree.branch 66 (VisitTree.leaf 65 [67]) (VisitTree.leaf 66 [68])))) (VisitTree.branch 76 (VisitTree.branch 72 (VisitTree.branch 71 (VisitTree.leaf 70 [150]) (VisitTree.leaf 71 [180])) (VisitTree.branch 73 (VisitTree.leaf 72 [74]) (VisitTree.leaf 73 [265]))) (VisitTree.branch 82 (VisitTree.branch 78 (VisitTree.leaf 76 [209]) (VisitTree.leaf 78 [264])) (VisitTree.branch 87 (VisitTree.leaf 82 [144]) (VisitTree.leaf 87 [189])))))) (VisitTree.branch 170 (VisitTree.branch 162 (VisitTree.branch 158 (VisitTree.branch 155 (VisitTree.branch 154 (VisitTree.leaf 153 [207]) (VisitTree.leaf 154 [159])) (VisitTree.branch 156 (VisitTree.leaf 155 [172]) (VisitTree.leaf 156 [265]))) (VisitTree.branch 160 (VisitTree.branch 159 (VisitTree.leaf 158 [124]) (VisitTree.leaf 159 [121])) (VisitTree.branch 161 (VisitTree.leaf 160 [149]) (VisitTree.leaf 161 [62])))) (VisitTree.branch 166 (VisitTree.branch 164 (VisitTree.branch 163 (VisitTree.leaf 162 [181]) (VisitTree.leaf 163 [119])) (VisitTree.branch 165 (VisitTree.leaf 164 [147]) (VisitTree.leaf 165 [48]))) (VisitTree.branch 168 (VisitTree.branch 167 (VisitTree.leaf 166 [178]) (VisitTree.leaf 167 [56])) (VisitTree.branch 169 (VisitTree.leaf 168 [67]) (VisitTree.leaf 169 [120]))))) (VisitTree.branch 181 (VisitTree.branch 176 (VisitTree.branch 174 (VisitTree.branch 173 (VisitTree.leaf 170 [150]) (VisitTree.leaf 173 [74])) (VisitTree.branch 175 (VisitTree.leaf 174 [63]) (VisitTree.leaf 175 [180]))) (VisitTree.branch 179 (VisitTree.branch 178 (VisitTree.leaf 176 [68]) (VisitTree.leaf 178 [52])) (VisitTree.branch 180 (VisitTree.leaf 179 [131]) (VisitTree.leaf 180 [129])))) (VisitTree.branch 187 (VisitTree.branch 184 (VisitTree.branch 182 (VisitTree.leaf 181 [146]) (VisitTree.leaf 182 [179])) (VisitTree.branch 186 (VisitTree.leaf 184 [264]) (VisitTree.leaf 186 [144]))) (VisitTree.branch 189 (VisitTree.branch 188 (VisitTree.leaf 187 [206]) (VisitTree.leaf 188 [189])) (VisitTree.branch 190 (VisitTree.leaf 189 [260]) (VisitTree.leaf 190 [209])))))))

def fastForwardChunkVisits076 (r : Nat) : List Nat :=
  forwardVisitTree076.lookup r

private theorem covered076 :
    visitsCovered forwardEventChunk076 forwardVisitTree076 = true := by
  decide +kernel

private theorem checked076 :
    visitsChecked forwardEventChunk076 forwardVisitTree076 = true := by
  decide +kernel

theorem eventVisits_forwardChunk076 (r : Nat) :
    eventVisits r forwardEventChunk076 = fastForwardChunkVisits076 r :=
  eventVisits_of_tree _ _ covered076 checked076 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk076

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 77. -/
def forwardVisitTree077 : VisitTree := (VisitTree.branch 110 (VisitTree.branch 28 (VisitTree.branch 16 (VisitTree.branch 10 (VisitTree.branch 4 (VisitTree.branch 2 (VisitTree.leaf 1 [212]) (VisitTree.leaf 2 [231])) (VisitTree.branch 7 (VisitTree.leaf 4 [230]) (VisitTree.leaf 7 [215]))) (VisitTree.branch 14 (VisitTree.branch 13 (VisitTree.leaf 10 [195]) (VisitTree.leaf 13 [194])) (VisitTree.branch 15 (VisitTree.leaf 14 [236]) (VisitTree.leaf 15 [134])))) (VisitTree.branch 22 (VisitTree.branch 19 (VisitTree.branch 18 (VisitTree.leaf 16 [243]) (VisitTree.leaf 18 [242])) (VisitTree.branch 20 (VisitTree.leaf 19 [152]) (VisitTree.leaf 20 [240]))) (VisitTree.branch 24 (VisitTree.branch 23 (VisitTree.leaf 22 [182]) (VisitTree.leaf 23 [137])) (VisitTree.branch 27 (VisitTree.leaf 24 [220]) (VisitTree.leaf 27 [156]))))) (VisitTree.branch 52 (VisitTree.branch 34 (VisitTree.branch 31 (VisitTree.branch 30 (VisitTree.leaf 28 [224]) (VisitTree.leaf 30 [140])) (VisitTree.branch 33 (VisitTree.leaf 31 [256]) (VisitTree.leaf 33 [185]))) (VisitTree.branch 44 (VisitTree.branch 37 (VisitTree.leaf 34 [204]) (VisitTree.leaf 37 [254])) (VisitTree.branch 47 (VisitTree.leaf 44 [170]) (VisitTree.leaf 47 [506])))) (VisitTree.branch 99 (VisitTree.branch 84 (VisitTree.branch 83 (VisitTree.leaf 52 [506]) (VisitTree.leaf 83 [201])) (VisitTree.branch 94 (VisitTree.leaf 84 [174]) (VisitTree.leaf 94 [167]))) (VisitTree.branch 102 (VisitTree.branch 100 (VisitTree.leaf 99 [219]) (VisitTree.leaf 100 [228])) (VisitTree.branch 105 (VisitTree.leaf 102 [166]) (VisitTree.leaf 105 [251])))))) (VisitTree.branch 206 (VisitTree.branch 198 (VisitTree.branch 194 (VisitTree.branch 192 (VisitTree.branch 191 (VisitTree.leaf 110 [250]) (VisitTree.leaf 191 [174])) (VisitTree.branch 193 (VisitTree.leaf 192 [256]) (VisitTree.leaf 193 [140]))) (VisitTree.branch 196 (VisitTree.branch 195 (VisitTree.leaf 194 [204]) (VisitTree.leaf 195 [170])) (VisitTree.branch 197 (VisitTree.leaf 196 [201]) (VisitTree.leaf 197 [254])))) (VisitTree.branch 202 (VisitTree.branch 200 (VisitTree.branch 199 (VisitTree.leaf 198 [185]) (VisitTree.leaf 199 [242])) (VisitTree.branch 201 (VisitTree.leaf 200 [156]) (VisitTree.leaf 201 [240]))) (VisitTree.branch 204 (VisitTree.branch 203 (VisitTree.leaf 202 [134]) (VisitTree.leaf 203 [182])) (VisitTree.branch 205 (VisitTree.leaf 204 [243]) (VisitTree.leaf 205 [166]))))) (VisitTree.branch 214 (VisitTree.branch 210 (VisitTree.branch 208 (VisitTree.branch 207 (VisitTree.leaf 206 [236]) (VisitTree.leaf 207 [137])) (VisitTree.branch 209 (VisitTree.leaf 208 [152]) (VisitTree.leaf 209 [228]))) (VisitTree.branch 212 (VisitTree.branch 211 (VisitTree.leaf 210 [220]) (VisitTree.leaf 211 [224])) (VisitTree.branch 213 (VisitTree.leaf 212 [219]) (VisitTree.leaf 213 [167])))) (VisitTree.branch 218 (VisitTree.branch 216 (VisitTree.branch 215 (VisitTree.leaf 214 [230]) (VisitTree.leaf 215 [194])) (VisitTree.branch 217 (VisitTree.leaf 216 [250]) (VisitTree.leaf 217 [212]))) (VisitTree.branch 220 (VisitTree.branch 219 (VisitTree.leaf 218 [195]) (VisitTree.leaf 219 [215])) (VisitTree.branch 221 (VisitTree.leaf 220 [231]) (VisitTree.leaf 221 [251])))))))

def fastForwardChunkVisits077 (r : Nat) : List Nat :=
  forwardVisitTree077.lookup r

private theorem covered077 :
    visitsCovered forwardEventChunk077 forwardVisitTree077 = true := by
  decide +kernel

private theorem checked077 :
    visitsChecked forwardEventChunk077 forwardVisitTree077 = true := by
  decide +kernel

theorem eventVisits_forwardChunk077 (r : Nat) :
    eventVisits r forwardEventChunk077 = fastForwardChunkVisits077 r :=
  eventVisits_of_tree _ _ covered077 checked077 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk077

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 78. -/
def forwardVisitTree078 : VisitTree := (VisitTree.branch 54 (VisitTree.branch 11 (VisitTree.branch 5 (VisitTree.branch 3 (VisitTree.leaf 0 [507]) (VisitTree.leaf 3 [507])) (VisitTree.branch 6 (VisitTree.leaf 5 [506, 506, 506, 506]) (VisitTree.branch 9 (VisitTree.leaf 6 [506, 506, 506]) (VisitTree.leaf 9 [506, 506, 506, 506])))) (VisitTree.branch 47 (VisitTree.branch 46 (VisitTree.leaf 11 [507]) (VisitTree.leaf 46 [506, 506, 506, 506, 506])) (VisitTree.branch 48 (VisitTree.leaf 47 [506, 506, 506]) (VisitTree.branch 52 (VisitTree.leaf 48 [506, 506, 506, 506, 506, 506]) (VisitTree.leaf 52 [506, 506, 506, 506, 506, 506, 506, 506, 506, 506, 506, 506, 506, 506, 506, 506]))))) (VisitTree.branch 63 (VisitTree.branch 58 (VisitTree.branch 56 (VisitTree.leaf 54 [506, 506, 506]) (VisitTree.leaf 56 [506, 506, 506])) (VisitTree.branch 61 (VisitTree.leaf 58 [506, 506, 506]) (VisitTree.branch 62 (VisitTree.leaf 61 [507]) (VisitTree.leaf 62 [507])))) (VisitTree.branch 69 (VisitTree.branch 68 (VisitTree.leaf 63 [507]) (VisitTree.leaf 68 [507, 507, 507, 507, 507])) (VisitTree.branch 72 (VisitTree.leaf 69 [507]) (VisitTree.branch 465 (VisitTree.leaf 72 [507]) (VisitTree.leaf 465 [507]))))))

def fastForwardChunkVisits078 (r : Nat) : List Nat :=
  forwardVisitTree078.lookup r

private theorem covered078 :
    visitsCovered forwardEventChunk078 forwardVisitTree078 = true := by
  decide +kernel

private theorem checked078 :
    visitsChecked forwardEventChunk078 forwardVisitTree078 = true := by
  decide +kernel

theorem eventVisits_forwardChunk078 (r : Nat) :
    eventVisits r forwardEventChunk078 = fastForwardChunkVisits078 r :=
  eventVisits_of_tree _ _ covered078 checked078 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk078

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 79. -/
def forwardVisitTree079 : VisitTree := (VisitTree.branch 59 (VisitTree.branch 30 (VisitTree.branch 3 (VisitTree.leaf 0 [507, 507, 507, 507, 507]) (VisitTree.branch 11 (VisitTree.leaf 3 [507, 507, 507, 507, 507, 507, 507]) (VisitTree.leaf 11 [507, 507, 507, 507]))) (VisitTree.branch 49 (VisitTree.branch 41 (VisitTree.leaf 30 [519]) (VisitTree.leaf 41 [519])) (VisitTree.branch 53 (VisitTree.leaf 49 [519]) (VisitTree.leaf 53 [519])))) (VisitTree.branch 68 (VisitTree.branch 62 (VisitTree.branch 61 (VisitTree.leaf 59 [519, 519, 519, 519]) (VisitTree.leaf 61 [507, 507, 507, 507, 507])) (VisitTree.branch 63 (VisitTree.leaf 62 [507, 507, 507, 507, 507, 507]) (VisitTree.leaf 63 [507, 507, 507, 507, 507, 507]))) (VisitTree.branch 72 (VisitTree.branch 69 (VisitTree.leaf 68 [507, 507, 507, 507, 507, 507, 507]) (VisitTree.leaf 69 [507, 507, 507, 507, 507, 507, 507, 507])) (VisitTree.branch 465 (VisitTree.leaf 72 [507, 507, 507, 507]) (VisitTree.leaf 465 [507, 507, 507, 507])))))

def fastForwardChunkVisits079 (r : Nat) : List Nat :=
  forwardVisitTree079.lookup r

private theorem covered079 :
    visitsCovered forwardEventChunk079 forwardVisitTree079 = true := by
  decide +kernel

private theorem checked079 :
    visitsChecked forwardEventChunk079 forwardVisitTree079 = true := by
  decide +kernel

theorem eventVisits_forwardChunk079 (r : Nat) :
    eventVisits r forwardEventChunk079 = fastForwardChunkVisits079 r :=
  eventVisits_of_tree _ _ covered079 checked079 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk079

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 80. -/
def forwardVisitTree080 : VisitTree := (VisitTree.branch 59 (VisitTree.branch 41 (VisitTree.branch 23 (VisitTree.leaf 15 [519, 519, 519, 519, 519, 519, 519, 519, 519]) (VisitTree.branch 30 (VisitTree.leaf 23 [519, 519, 519, 519]) (VisitTree.leaf 30 [519, 519, 519]))) (VisitTree.branch 49 (VisitTree.leaf 41 [519, 519, 519, 519, 519]) (VisitTree.branch 53 (VisitTree.leaf 49 [519, 519, 519]) (VisitTree.leaf 53 [519, 519, 519, 519, 519, 519])))) (VisitTree.branch 82 (VisitTree.branch 70 (VisitTree.leaf 59 [519, 519, 519, 519, 519, 519, 519, 519, 519]) (VisitTree.branch 75 (VisitTree.leaf 70 [519, 519, 519, 519, 519, 519]) (VisitTree.leaf 75 [519, 519, 519, 519, 519, 519, 519, 519]))) (VisitTree.branch 91 (VisitTree.leaf 82 [519, 519, 519, 519, 519, 519, 519]) (VisitTree.branch 96 (VisitTree.leaf 91 [519]) (VisitTree.leaf 96 [519, 519, 519])))))

def fastForwardChunkVisits080 (r : Nat) : List Nat :=
  forwardVisitTree080.lookup r

private theorem covered080 :
    visitsCovered forwardEventChunk080 forwardVisitTree080 = true := by
  decide +kernel

private theorem checked080 :
    visitsChecked forwardEventChunk080 forwardVisitTree080 = true := by
  decide +kernel

theorem eventVisits_forwardChunk080 (r : Nat) :
    eventVisits r forwardEventChunk080 = fastForwardChunkVisits080 r :=
  eventVisits_of_tree _ _ covered080 checked080 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk080

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 81. -/
def forwardVisitTree081 : VisitTree := (VisitTree.branch 59 (VisitTree.branch 35 (VisitTree.branch 27 (VisitTree.branch 19 (VisitTree.leaf 15 [519, 519, 519]) (VisitTree.leaf 19 [508, 508, 508, 508, 508])) (VisitTree.branch 30 (VisitTree.leaf 27 [508, 508]) (VisitTree.leaf 30 [519, 519]))) (VisitTree.branch 49 (VisitTree.branch 43 (VisitTree.leaf 35 [508, 508, 508]) (VisitTree.leaf 43 [508, 508, 508, 508, 508, 508])) (VisitTree.branch 57 (VisitTree.leaf 49 [519, 519, 519]) (VisitTree.leaf 57 [508, 508])))) (VisitTree.branch 89 (VisitTree.branch 66 (VisitTree.branch 65 (VisitTree.leaf 59 [519, 519, 519]) (VisitTree.leaf 65 [508, 508])) (VisitTree.branch 74 (VisitTree.leaf 66 [508, 508, 508, 508, 508, 508, 508, 508]) (VisitTree.leaf 74 [508, 508, 508, 508, 508]))) (VisitTree.branch 97 (VisitTree.branch 91 (VisitTree.leaf 89 [508, 508, 508, 508, 508, 508, 508, 508]) (VisitTree.leaf 91 [519])) (VisitTree.branch 466 (VisitTree.leaf 97 [508, 508, 508, 508, 508, 508, 508, 508, 508]) (VisitTree.leaf 466 [508, 508])))))

def fastForwardChunkVisits081 (r : Nat) : List Nat :=
  forwardVisitTree081.lookup r

private theorem covered081 :
    visitsCovered forwardEventChunk081 forwardVisitTree081 = true := by
  decide +kernel

private theorem checked081 :
    visitsChecked forwardEventChunk081 forwardVisitTree081 = true := by
  decide +kernel

theorem eventVisits_forwardChunk081 (r : Nat) :
    eventVisits r forwardEventChunk081 = fastForwardChunkVisits081 r :=
  eventVisits_of_tree _ _ covered081 checked081 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk081

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 82. -/
def forwardVisitTree082 : VisitTree := (VisitTree.branch 64 (VisitTree.branch 36 (VisitTree.branch 27 (VisitTree.branch 26 (VisitTree.leaf 21 [520, 520, 520]) (VisitTree.leaf 26 [520, 520, 520])) (VisitTree.branch 35 (VisitTree.leaf 27 [508, 508]) (VisitTree.leaf 35 [508, 508, 508, 508]))) (VisitTree.branch 44 (VisitTree.branch 43 (VisitTree.leaf 36 [520, 520, 520]) (VisitTree.leaf 43 [508, 508])) (VisitTree.branch 51 (VisitTree.leaf 44 [520, 520, 520, 520, 520, 520, 520, 520]) (VisitTree.branch 55 (VisitTree.leaf 51 [520]) (VisitTree.leaf 55 [520, 520, 520, 520, 520, 520, 520, 520]))))) (VisitTree.branch 84 (VisitTree.branch 71 (VisitTree.branch 66 (VisitTree.leaf 64 [520, 520]) (VisitTree.leaf 66 [508, 508, 508, 508, 508])) (VisitTree.branch 74 (VisitTree.leaf 71 [520, 520]) (VisitTree.branch 80 (VisitTree.leaf 74 [508, 508, 508]) (VisitTree.leaf 80 [520, 520, 520, 520])))) (VisitTree.branch 94 (VisitTree.branch 89 (VisitTree.leaf 84 [520, 520, 520, 520]) (VisitTree.leaf 89 [508, 508, 508, 508])) (VisitTree.branch 102 (VisitTree.leaf 94 [520, 520]) (VisitTree.branch 466 (VisitTree.leaf 102 [520, 520]) (VisitTree.leaf 466 [508, 508]))))))

def fastForwardChunkVisits082 (r : Nat) : List Nat :=
  forwardVisitTree082.lookup r

private theorem covered082 :
    visitsCovered forwardEventChunk082 forwardVisitTree082 = true := by
  decide +kernel

private theorem checked082 :
    visitsChecked forwardEventChunk082 forwardVisitTree082 = true := by
  decide +kernel

theorem eventVisits_forwardChunk082 (r : Nat) :
    eventVisits r forwardEventChunk082 = fastForwardChunkVisits082 r :=
  eventVisits_of_tree _ _ covered082 checked082 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk082

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 83. -/
def forwardVisitTree083 : VisitTree := (VisitTree.branch 60 (VisitTree.branch 36 (VisitTree.branch 22 (VisitTree.branch 21 (VisitTree.leaf 17 [509]) (VisitTree.leaf 21 [520, 520, 520])) (VisitTree.branch 26 (VisitTree.leaf 22 [509, 509]) (VisitTree.branch 33 (VisitTree.leaf 26 [520, 520, 520, 520]) (VisitTree.leaf 33 [509, 509, 509])))) (VisitTree.branch 50 (VisitTree.branch 38 (VisitTree.leaf 36 [520, 520, 520]) (VisitTree.branch 44 (VisitTree.leaf 38 [509, 509]) (VisitTree.leaf 44 [520, 520, 520, 520, 520, 520]))) (VisitTree.branch 51 (VisitTree.leaf 50 [509]) (VisitTree.branch 55 (VisitTree.leaf 51 [520, 520, 520, 520]) (VisitTree.leaf 55 [520, 520, 520, 520, 520, 520]))))) (VisitTree.branch 80 (VisitTree.branch 67 (VisitTree.branch 64 (VisitTree.leaf 60 [509]) (VisitTree.leaf 64 [520, 520])) (VisitTree.branch 71 (VisitTree.leaf 67 [509]) (VisitTree.branch 77 (VisitTree.leaf 71 [520, 520]) (VisitTree.leaf 77 [509, 509])))) (VisitTree.branch 92 (VisitTree.branch 84 (VisitTree.leaf 80 [520, 520]) (VisitTree.branch 87 (VisitTree.leaf 84 [520]) (VisitTree.leaf 87 [509, 509, 509, 509, 509, 509, 509, 509]))) (VisitTree.branch 94 (VisitTree.leaf 92 [509, 509, 509]) (VisitTree.branch 102 (VisitTree.leaf 94 [520, 520, 520, 520]) (VisitTree.leaf 102 [520, 520, 520]))))))

def fastForwardChunkVisits083 (r : Nat) : List Nat :=
  forwardVisitTree083.lookup r

private theorem covered083 :
    visitsCovered forwardEventChunk083 forwardVisitTree083 = true := by
  decide +kernel

private theorem checked083 :
    visitsChecked forwardEventChunk083 forwardVisitTree083 = true := by
  decide +kernel

theorem eventVisits_forwardChunk083 (r : Nat) :
    eventVisits r forwardEventChunk083 = fastForwardChunkVisits083 r :=
  eventVisits_of_tree _ _ covered083 checked083 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk083


