-- Prove2me | Definitions.Def_CSL_Generated_MemoryAccess_Group08
-- name    : CSL_Generated_MemoryAccess_Group08
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T13:31:56.165821+00:00
-- url     : https://prove2.me/theorems/aecfabc7-9449-438f-8094-aac262374b4e
-- title:
--   Coded sorting library: Generated / MemoryAccess / Group08
-- statement:
--   Module `CodedSorting.Generated.MemoryAccess.Group08` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Generated.MemoryAccess.Group08

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Circuit_MemoryAccess_PhysicalFrameEventChunkData
import Definitions.Def_CSL_Generated_MemoryAccess_Base

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 132. -/
def forwardVisitTree132 : VisitTree := (VisitTree.branch 572 (VisitTree.branch 551 (VisitTree.branch 518 (VisitTree.leaf 517 [1, 1, 1, 1, 1, 1]) (VisitTree.branch 536 (VisitTree.leaf 518 [1, 1, 1, 1]) (VisitTree.leaf 536 [1, 1, 1, 1, 1, 1]))) (VisitTree.branch 554 (VisitTree.leaf 551 [1, 1]) (VisitTree.branch 558 (VisitTree.leaf 554 [1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 558 [1, 1, 1, 1])))) (VisitTree.branch 612 (VisitTree.branch 584 (VisitTree.leaf 572 [1, 1, 1, 1, 1, 1, 1]) (VisitTree.branch 603 (VisitTree.leaf 584 [1, 1, 1, 1, 1]) (VisitTree.leaf 603 [1, 1, 1, 1]))) (VisitTree.branch 625 (VisitTree.leaf 612 [1, 1, 1, 1, 1, 1]) (VisitTree.branch 651 (VisitTree.leaf 625 [1, 1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 651 [1, 1, 1, 1, 1])))))

def fastForwardChunkVisits132 (r : Nat) : List Nat :=
  forwardVisitTree132.lookup r

private theorem covered132 :
    visitsCovered forwardEventChunk132 forwardVisitTree132 = true := by
  decide +kernel

private theorem checked132 :
    visitsChecked forwardEventChunk132 forwardVisitTree132 = true := by
  decide +kernel

theorem eventVisits_forwardChunk132 (r : Nat) :
    eventVisits r forwardEventChunk132 = fastForwardChunkVisits132 r :=
  eventVisits_of_tree _ _ covered132 checked132 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk132

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 133. -/
def forwardVisitTree133 : VisitTree := (VisitTree.branch 591 (VisitTree.branch 554 (VisitTree.branch 520 (VisitTree.branch 519 (VisitTree.leaf 518 [1, 1, 1]) (VisitTree.leaf 519 [1, 1, 1, 1, 1, 1, 1, 1])) (VisitTree.branch 536 (VisitTree.leaf 520 [1, 1]) (VisitTree.leaf 536 [1, 1]))) (VisitTree.branch 556 (VisitTree.branch 555 (VisitTree.leaf 554 [1, 1]) (VisitTree.leaf 555 [1, 1, 1, 1, 1, 1, 1, 1])) (VisitTree.branch 572 (VisitTree.leaf 556 [1, 1, 1]) (VisitTree.leaf 572 [1])))) (VisitTree.branch 618 (VisitTree.branch 612 (VisitTree.branch 592 (VisitTree.leaf 591 [1, 1, 1]) (VisitTree.leaf 592 [1, 1, 1, 1, 1, 1])) (VisitTree.branch 613 (VisitTree.leaf 612 [1]) (VisitTree.leaf 613 [1, 1, 1, 1, 1, 1, 1]))) (VisitTree.branch 637 (VisitTree.branch 625 (VisitTree.leaf 618 [1, 1]) (VisitTree.leaf 625 [1])) (VisitTree.branch 642 (VisitTree.leaf 637 [1, 1]) (VisitTree.branch 645 (VisitTree.leaf 642 [1, 1, 1, 1, 1, 1]) (VisitTree.leaf 645 [1, 1, 1, 1, 1, 1, 1]))))))

def fastForwardChunkVisits133 (r : Nat) : List Nat :=
  forwardVisitTree133.lookup r

private theorem covered133 :
    visitsCovered forwardEventChunk133 forwardVisitTree133 = true := by
  decide +kernel

private theorem checked133 :
    visitsChecked forwardEventChunk133 forwardVisitTree133 = true := by
  decide +kernel

theorem eventVisits_forwardChunk133 (r : Nat) :
    eventVisits r forwardEventChunk133 = fastForwardChunkVisits133 r :=
  eventVisits_of_tree _ _ covered133 checked133 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk133

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 134. -/
def forwardVisitTree134 : VisitTree := (VisitTree.branch 591 (VisitTree.branch 556 (VisitTree.branch 521 (VisitTree.leaf 520 [1, 1, 1, 1, 1, 1]) (VisitTree.branch 539 (VisitTree.leaf 521 [1, 1, 1, 1]) (VisitTree.leaf 539 [1, 1, 1, 1, 1, 1, 1]))) (VisitTree.branch 557 (VisitTree.leaf 556 [1, 1, 1, 1, 1]) (VisitTree.branch 575 (VisitTree.leaf 557 [1, 1, 1, 1, 1]) (VisitTree.leaf 575 [1, 1, 1, 1, 1])))) (VisitTree.branch 630 (VisitTree.branch 607 (VisitTree.leaf 591 [1, 1, 1, 1]) (VisitTree.branch 618 (VisitTree.leaf 607 [1, 1, 1, 1, 1, 1]) (VisitTree.leaf 618 [1, 1, 1, 1]))) (VisitTree.branch 637 (VisitTree.leaf 630 [1, 1, 1, 1, 1, 1, 1]) (VisitTree.branch 646 (VisitTree.leaf 637 [1, 1, 1, 1]) (VisitTree.leaf 646 [1, 1, 1, 1, 1, 1, 1])))))

def fastForwardChunkVisits134 (r : Nat) : List Nat :=
  forwardVisitTree134.lookup r

private theorem covered134 :
    visitsCovered forwardEventChunk134 forwardVisitTree134 = true := by
  decide +kernel

private theorem checked134 :
    visitsChecked forwardEventChunk134 forwardVisitTree134 = true := by
  decide +kernel

theorem eventVisits_forwardChunk134 (r : Nat) :
    eventVisits r forwardEventChunk134 = fastForwardChunkVisits134 r :=
  eventVisits_of_tree _ _ covered134 checked134 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk134

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 135. -/
def forwardVisitTree135 : VisitTree := (VisitTree.branch 548 (VisitTree.branch 493 (VisitTree.branch 448 (VisitTree.branch 363 (VisitTree.leaf 350 [1, 1, 1]) (VisitTree.leaf 363 [1, 1, 1])) (VisitTree.branch 450 (VisitTree.leaf 448 [1, 1, 1, 1]) (VisitTree.leaf 450 [1, 1, 1, 1, 1, 1]))) (VisitTree.branch 521 (VisitTree.branch 516 (VisitTree.leaf 493 [1, 1, 1, 1]) (VisitTree.leaf 516 [1, 1, 1, 1])) (VisitTree.branch 522 (VisitTree.leaf 521 [1, 1, 1, 1]) (VisitTree.leaf 522 [1, 1, 1, 1, 1, 1, 1])))) (VisitTree.branch 587 (VisitTree.branch 557 (VisitTree.branch 553 (VisitTree.leaf 548 [1, 1, 1, 1, 1, 1]) (VisitTree.leaf 553 [1, 1])) (VisitTree.branch 575 (VisitTree.leaf 557 [1]) (VisitTree.leaf 575 [1]))) (VisitTree.branch 607 (VisitTree.branch 604 (VisitTree.leaf 587 [1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 604 [1, 1, 1, 1, 1])) (VisitTree.branch 630 (VisitTree.leaf 607 [1]) (VisitTree.branch 652 (VisitTree.leaf 630 [1]) (VisitTree.leaf 652 [1, 1, 1, 1, 1]))))))

def fastForwardChunkVisits135 (r : Nat) : List Nat :=
  forwardVisitTree135.lookup r

private theorem covered135 :
    visitsCovered forwardEventChunk135 forwardVisitTree135 = true := by
  decide +kernel

private theorem checked135 :
    visitsChecked forwardEventChunk135 forwardVisitTree135 = true := by
  decide +kernel

theorem eventVisits_forwardChunk135 (r : Nat) :
    eventVisits r forwardEventChunk135 = fastForwardChunkVisits135 r :=
  eventVisits_of_tree _ _ covered135 checked135 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk135

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 136. -/
def forwardVisitTree136 : VisitTree := (VisitTree.branch 448 (VisitTree.branch 330 (VisitTree.branch 320 (VisitTree.leaf 225 [1, 1, 1, 1, 1, 1, 1]) (VisitTree.branch 328 (VisitTree.leaf 320 [1, 1, 1, 1, 1, 1]) (VisitTree.leaf 328 [1, 1, 1, 1, 1, 1, 1]))) (VisitTree.branch 350 (VisitTree.leaf 330 [1, 1, 1, 1, 1, 1]) (VisitTree.branch 363 (VisitTree.leaf 350 [1, 1, 1, 1]) (VisitTree.leaf 363 [1, 1, 1, 1])))) (VisitTree.branch 493 (VisitTree.branch 450 (VisitTree.leaf 448 [1, 1, 1, 1]) (VisitTree.branch 458 (VisitTree.leaf 450 [1, 1]) (VisitTree.leaf 458 [1, 1, 1, 1, 1, 1, 1, 1]))) (VisitTree.branch 511 (VisitTree.leaf 493 [1, 1, 1, 1]) (VisitTree.branch 516 (VisitTree.leaf 511 [1, 1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 516 [1, 1, 1, 1])))))

def fastForwardChunkVisits136 (r : Nat) : List Nat :=
  forwardVisitTree136.lookup r

private theorem covered136 :
    visitsCovered forwardEventChunk136 forwardVisitTree136 = true := by
  decide +kernel

private theorem checked136 :
    visitsChecked forwardEventChunk136 forwardVisitTree136 = true := by
  decide +kernel

theorem eventVisits_forwardChunk136 (r : Nat) :
    eventVisits r forwardEventChunk136 = fastForwardChunkVisits136 r :=
  eventVisits_of_tree _ _ covered136 checked136 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk136

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 137. -/
def forwardVisitTree137 : VisitTree := (VisitTree.branch 388 (VisitTree.branch 320 (VisitTree.branch 301 (VisitTree.leaf 262 [1, 1, 1, 1, 1, 1, 1, 1]) (VisitTree.branch 314 (VisitTree.leaf 301 [1, 1, 1]) (VisitTree.leaf 314 [1, 1, 1, 1, 1, 1]))) (VisitTree.branch 328 (VisitTree.branch 321 (VisitTree.leaf 320 [1, 1]) (VisitTree.leaf 321 [1, 1, 1, 1])) (VisitTree.branch 330 (VisitTree.leaf 328 [1]) (VisitTree.leaf 330 [1])))) (VisitTree.branch 440 (VisitTree.branch 422 (VisitTree.branch 402 (VisitTree.leaf 388 [1, 1, 1]) (VisitTree.leaf 402 [1, 1, 1, 1, 1, 1, 1, 1])) (VisitTree.branch 432 (VisitTree.leaf 422 [1, 1, 1]) (VisitTree.leaf 432 [1]))) (VisitTree.branch 512 (VisitTree.branch 494 (VisitTree.leaf 440 [1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 494 [1, 1, 1, 1, 1, 1, 1, 1])) (VisitTree.branch 515 (VisitTree.leaf 512 [1, 1, 1, 1, 1]) (VisitTree.leaf 515 [1, 1, 1, 1])))))

def fastForwardChunkVisits137 (r : Nat) : List Nat :=
  forwardVisitTree137.lookup r

private theorem covered137 :
    visitsCovered forwardEventChunk137 forwardVisitTree137 = true := by
  decide +kernel

private theorem checked137 :
    visitsChecked forwardEventChunk137 forwardVisitTree137 = true := by
  decide +kernel

theorem eventVisits_forwardChunk137 (r : Nat) :
    eventVisits r forwardEventChunk137 = fastForwardChunkVisits137 r :=
  eventVisits_of_tree _ _ covered137 checked137 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk137

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 138. -/
def forwardVisitTree138 : VisitTree := (VisitTree.branch 384 (VisitTree.branch 301 (VisitTree.branch 279 (VisitTree.leaf 267 [1, 1, 1, 1, 1, 1]) (VisitTree.branch 291 (VisitTree.leaf 279 [1]) (VisitTree.leaf 291 [1, 1, 1, 1, 1]))) (VisitTree.branch 321 (VisitTree.branch 317 (VisitTree.leaf 301 [1, 1, 1]) (VisitTree.leaf 317 [1, 1, 1, 1, 1, 1, 1, 1, 1])) (VisitTree.branch 348 (VisitTree.leaf 321 [1, 1, 1, 1]) (VisitTree.leaf 348 [1])))) (VisitTree.branch 438 (VisitTree.branch 422 (VisitTree.branch 388 (VisitTree.leaf 384 [1, 1]) (VisitTree.leaf 388 [1, 1, 1, 1])) (VisitTree.branch 432 (VisitTree.leaf 422 [1, 1, 1, 1]) (VisitTree.leaf 432 [1, 1, 1, 1]))) (VisitTree.branch 513 (VisitTree.branch 495 (VisitTree.leaf 438 [1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 495 [1, 1, 1, 1, 1, 1, 1, 1])) (VisitTree.branch 515 (VisitTree.leaf 513 [1, 1, 1, 1, 1]) (VisitTree.leaf 515 [1])))))

def fastForwardChunkVisits138 (r : Nat) : List Nat :=
  forwardVisitTree138.lookup r

private theorem covered138 :
    visitsCovered forwardEventChunk138 forwardVisitTree138 = true := by
  decide +kernel

private theorem checked138 :
    visitsChecked forwardEventChunk138 forwardVisitTree138 = true := by
  decide +kernel

theorem eventVisits_forwardChunk138 (r : Nat) :
    eventVisits r forwardEventChunk138 = fastForwardChunkVisits138 r :=
  eventVisits_of_tree _ _ covered138 checked138 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk138

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 139. -/
def forwardVisitTree139 : VisitTree := (VisitTree.branch 372 (VisitTree.branch 303 (VisitTree.branch 279 (VisitTree.leaf 269 [1, 1, 1, 1, 1, 1]) (VisitTree.branch 292 (VisitTree.leaf 279 [1, 1, 1, 1, 1, 1]) (VisitTree.leaf 292 [1, 1, 1, 1, 1, 1]))) (VisitTree.branch 313 (VisitTree.leaf 303 [1, 1, 1, 1, 1, 1]) (VisitTree.branch 348 (VisitTree.leaf 313 [1, 1, 1, 1]) (VisitTree.leaf 348 [1, 1, 1, 1, 1, 1])))) (VisitTree.branch 430 (VisitTree.branch 384 (VisitTree.leaf 372 [1, 1, 1, 1]) (VisitTree.branch 420 (VisitTree.leaf 384 [1, 1, 1, 1, 1]) (VisitTree.leaf 420 [1, 1, 1, 1, 1, 1]))) (VisitTree.branch 496 (VisitTree.leaf 430 [1, 1, 1, 1, 1, 1]) (VisitTree.branch 514 (VisitTree.leaf 496 [1, 1, 1, 1]) (VisitTree.leaf 514 [1, 1, 1, 1, 1])))))

def fastForwardChunkVisits139 (r : Nat) : List Nat :=
  forwardVisitTree139.lookup r

private theorem covered139 :
    visitsCovered forwardEventChunk139 forwardVisitTree139 = true := by
  decide +kernel

private theorem checked139 :
    visitsChecked forwardEventChunk139 forwardVisitTree139 = true := by
  decide +kernel

theorem eventVisits_forwardChunk139 (r : Nat) :
    eventVisits r forwardEventChunk139 = fastForwardChunkVisits139 r :=
  eventVisits_of_tree _ _ covered139 checked139 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk139

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 140. -/
def forwardVisitTree140 : VisitTree := (VisitTree.branch 336 (VisitTree.branch 289 (VisitTree.branch 269 (VisitTree.branch 264 (VisitTree.leaf 255 [1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 264 [1])) (VisitTree.branch 282 (VisitTree.leaf 269 [1, 1]) (VisitTree.leaf 282 [1, 1, 1, 1, 1, 1]))) (VisitTree.branch 306 (VisitTree.branch 292 (VisitTree.leaf 289 [1]) (VisitTree.leaf 292 [1, 1])) (VisitTree.branch 313 (VisitTree.leaf 306 [1, 1, 1, 1, 1, 1]) (VisitTree.leaf 313 [1, 1])))) (VisitTree.branch 409 (VisitTree.branch 372 (VisitTree.branch 367 (VisitTree.leaf 336 [1, 1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 367 [1, 1, 1, 1, 1])) (VisitTree.branch 395 (VisitTree.leaf 372 [1, 1, 1, 1]) (VisitTree.leaf 395 [1, 1]))) (VisitTree.branch 445 (VisitTree.branch 420 (VisitTree.leaf 409 [1, 1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 420 [1, 1])) (VisitTree.branch 496 (VisitTree.leaf 445 [1, 1]) (VisitTree.branch 497 (VisitTree.leaf 496 [1, 1, 1, 1]) (VisitTree.leaf 497 [1, 1]))))))

def fastForwardChunkVisits140 (r : Nat) : List Nat :=
  forwardVisitTree140.lookup r

private theorem covered140 :
    visitsCovered forwardEventChunk140 forwardVisitTree140 = true := by
  decide +kernel

private theorem checked140 :
    visitsChecked forwardEventChunk140 forwardVisitTree140 = true := by
  decide +kernel

theorem eventVisits_forwardChunk140 (r : Nat) :
    eventVisits r forwardEventChunk140 = fastForwardChunkVisits140 r :=
  eventVisits_of_tree _ _ covered140 checked140 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk140

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 141. -/
def forwardVisitTree141 : VisitTree := (VisitTree.branch 387 (VisitTree.branch 323 (VisitTree.branch 285 (VisitTree.leaf 264 [1, 1, 1, 1, 1]) (VisitTree.branch 289 (VisitTree.leaf 285 [1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 289 [1, 1, 1, 1, 1]))) (VisitTree.branch 361 (VisitTree.leaf 323 [1, 1, 1, 1, 1, 1]) (VisitTree.branch 366 (VisitTree.leaf 361 [1, 1, 1, 1, 1]) (VisitTree.leaf 366 [1, 1, 1, 1, 1])))) (VisitTree.branch 424 (VisitTree.branch 395 (VisitTree.leaf 387 [1, 1, 1, 1]) (VisitTree.branch 406 (VisitTree.leaf 395 [1, 1, 1, 1, 1]) (VisitTree.leaf 406 [1, 1, 1, 1, 1, 1]))) (VisitTree.branch 445 (VisitTree.leaf 424 [1, 1, 1, 1, 1, 1, 1, 1]) (VisitTree.branch 497 (VisitTree.leaf 445 [1, 1, 1]) (VisitTree.leaf 497 [1, 1, 1, 1, 1])))))

def fastForwardChunkVisits141 (r : Nat) : List Nat :=
  forwardVisitTree141.lookup r

private theorem covered141 :
    visitsCovered forwardEventChunk141 forwardVisitTree141 = true := by
  decide +kernel

private theorem checked141 :
    visitsChecked forwardEventChunk141 forwardVisitTree141 = true := by
  decide +kernel

theorem eventVisits_forwardChunk141 (r : Nat) :
    eventVisits r forwardEventChunk141 = fastForwardChunkVisits141 r :=
  eventVisits_of_tree _ _ covered141 checked141 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk141

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 142. -/
def forwardVisitTree142 : VisitTree := (VisitTree.branch 376 (VisitTree.branch 337 (VisitTree.branch 251 (VisitTree.leaf 230 [1, 1, 1]) (VisitTree.branch 323 (VisitTree.leaf 251 [1, 1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 323 [1, 1]))) (VisitTree.branch 356 (VisitTree.branch 347 (VisitTree.leaf 337 [1, 1]) (VisitTree.leaf 347 [1, 1, 1])) (VisitTree.branch 370 (VisitTree.leaf 356 [1, 1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 370 [1, 1, 1])))) (VisitTree.branch 406 (VisitTree.branch 378 (VisitTree.leaf 376 [1, 1, 1, 1, 1, 1, 1]) (VisitTree.branch 387 (VisitTree.leaf 378 [1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 387 [1]))) (VisitTree.branch 460 (VisitTree.branch 453 (VisitTree.leaf 406 [1]) (VisitTree.leaf 453 [1, 1, 1])) (VisitTree.branch 498 (VisitTree.leaf 460 [1, 1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 498 [1, 1, 1, 1, 1, 1, 1, 1])))))

def fastForwardChunkVisits142 (r : Nat) : List Nat :=
  forwardVisitTree142.lookup r

private theorem covered142 :
    visitsCovered forwardEventChunk142 forwardVisitTree142 = true := by
  decide +kernel

private theorem checked142 :
    visitsChecked forwardEventChunk142 forwardVisitTree142 = true := by
  decide +kernel

theorem eventVisits_forwardChunk142 (r : Nat) :
    eventVisits r forwardEventChunk142 = fastForwardChunkVisits142 r :=
  eventVisits_of_tree _ _ covered142 checked142 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk142

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 143. -/
def forwardVisitTree143 : VisitTree := (VisitTree.branch 370 (VisitTree.branch 337 (VisitTree.branch 239 (VisitTree.leaf 230 [1, 1, 1, 1, 1]) (VisitTree.branch 335 (VisitTree.leaf 239 [1, 1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 335 [1, 1, 1, 1, 1, 1]))) (VisitTree.branch 347 (VisitTree.leaf 337 [1, 1, 1, 1, 1]) (VisitTree.branch 364 (VisitTree.leaf 347 [1, 1, 1, 1]) (VisitTree.leaf 364 [1, 1, 1, 1, 1, 1, 1])))) (VisitTree.branch 454 (VisitTree.branch 373 (VisitTree.leaf 370 [1, 1, 1]) (VisitTree.branch 453 (VisitTree.leaf 373 [1, 1, 1, 1, 1]) (VisitTree.leaf 453 [1, 1, 1, 1]))) (VisitTree.branch 487 (VisitTree.leaf 454 [1, 1, 1, 1, 1, 1, 1]) (VisitTree.branch 510 (VisitTree.leaf 487 [1, 1, 1, 1, 1, 1]) (VisitTree.leaf 510 [1, 1, 1, 1])))))

def fastForwardChunkVisits143 (r : Nat) : List Nat :=
  forwardVisitTree143.lookup r

private theorem covered143 :
    visitsCovered forwardEventChunk143 forwardVisitTree143 = true := by
  decide +kernel

private theorem checked143 :
    visitsChecked forwardEventChunk143 forwardVisitTree143 = true := by
  decide +kernel

theorem eventVisits_forwardChunk143 (r : Nat) :
    eventVisits r forwardEventChunk143 = fastForwardChunkVisits143 r :=
  eventVisits_of_tree _ _ covered143 checked143 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk143

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 144. -/
def forwardVisitTree144 : VisitTree := (VisitTree.branch 362 (VisitTree.branch 286 (VisitTree.branch 265 (VisitTree.leaf 224 [1, 1, 1, 1, 1]) (VisitTree.branch 270 (VisitTree.leaf 265 [1, 1, 1, 1, 1]) (VisitTree.leaf 270 [1, 1, 1, 1, 1, 1]))) (VisitTree.branch 324 (VisitTree.branch 315 (VisitTree.leaf 286 [1, 1, 1]) (VisitTree.leaf 315 [1, 1, 1, 1])) (VisitTree.branch 326 (VisitTree.leaf 324 [1, 1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 326 [1, 1, 1, 1, 1, 1, 1])))) (VisitTree.branch 488 (VisitTree.branch 446 (VisitTree.leaf 362 [1, 1, 1, 1, 1]) (VisitTree.branch 487 (VisitTree.leaf 446 [1, 1, 1, 1, 1]) (VisitTree.leaf 487 [1]))) (VisitTree.branch 506 (VisitTree.branch 505 (VisitTree.leaf 488 [1, 1, 1, 1]) (VisitTree.leaf 505 [1, 1, 1, 1, 1, 1])) (VisitTree.branch 510 (VisitTree.leaf 506 [1, 1, 1, 1]) (VisitTree.leaf 510 [1])))))

def fastForwardChunkVisits144 (r : Nat) : List Nat :=
  forwardVisitTree144.lookup r

private theorem covered144 :
    visitsCovered forwardEventChunk144 forwardVisitTree144 = true := by
  decide +kernel

private theorem checked144 :
    visitsChecked forwardEventChunk144 forwardVisitTree144 = true := by
  decide +kernel

theorem eventVisits_forwardChunk144 (r : Nat) :
    eventVisits r forwardEventChunk144 = fastForwardChunkVisits144 r :=
  eventVisits_of_tree _ _ covered144 checked144 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk144

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 145. -/
def forwardVisitTree145 : VisitTree := (VisitTree.branch 414 (VisitTree.branch 300 (VisitTree.branch 270 (VisitTree.leaf 265 [1, 1, 1]) (VisitTree.branch 286 (VisitTree.leaf 270 [1, 1]) (VisitTree.leaf 286 [1, 1, 1]))) (VisitTree.branch 315 (VisitTree.branch 305 (VisitTree.leaf 300 [1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 305 [1, 1, 1, 1, 1, 1, 1])) (VisitTree.branch 318 (VisitTree.leaf 315 [1, 1, 1, 1]) (VisitTree.leaf 318 [1, 1, 1, 1, 1, 1, 1])))) (VisitTree.branch 489 (VisitTree.branch 441 (VisitTree.branch 431 (VisitTree.leaf 414 [1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 431 [1, 1])) (VisitTree.branch 488 (VisitTree.leaf 441 [1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 488 [1, 1, 1, 1]))) (VisitTree.branch 507 (VisitTree.branch 506 (VisitTree.leaf 489 [1]) (VisitTree.leaf 506 [1, 1, 1, 1])) (VisitTree.branch 509 (VisitTree.leaf 507 [1]) (VisitTree.leaf 509 [1, 1, 1, 1, 1])))))

def fastForwardChunkVisits145 (r : Nat) : List Nat :=
  forwardVisitTree145.lookup r

private theorem covered145 :
    visitsCovered forwardEventChunk145 forwardVisitTree145 = true := by
  decide +kernel

private theorem checked145 :
    visitsChecked forwardEventChunk145 forwardVisitTree145 = true := by
  decide +kernel

theorem eventVisits_forwardChunk145 (r : Nat) :
    eventVisits r forwardEventChunk145 = fastForwardChunkVisits145 r :=
  eventVisits_of_tree _ _ covered145 checked145 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk145

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 146. -/
def forwardVisitTree146 : VisitTree := (VisitTree.branch 418 (VisitTree.branch 390 (VisitTree.branch 344 (VisitTree.leaf 283 [1, 1, 1]) (VisitTree.branch 383 (VisitTree.leaf 344 [1, 1, 1, 1]) (VisitTree.leaf 383 [1, 1, 1, 1, 1, 1, 1, 1]))) (VisitTree.branch 400 (VisitTree.leaf 390 [1, 1, 1]) (VisitTree.branch 408 (VisitTree.leaf 400 [1, 1, 1]) (VisitTree.leaf 408 [1, 1, 1, 1, 1, 1, 1, 1])))) (VisitTree.branch 489 (VisitTree.branch 426 (VisitTree.leaf 418 [1, 1, 1]) (VisitTree.branch 431 (VisitTree.leaf 426 [1, 1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 431 [1, 1, 1, 1, 1, 1]))) (VisitTree.branch 507 (VisitTree.leaf 489 [1, 1, 1, 1, 1, 1, 1]) (VisitTree.branch 508 (VisitTree.leaf 507 [1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 508 [1, 1, 1, 1])))))

def fastForwardChunkVisits146 (r : Nat) : List Nat :=
  forwardVisitTree146.lookup r

private theorem covered146 :
    visitsCovered forwardEventChunk146 forwardVisitTree146 = true := by
  decide +kernel

private theorem checked146 :
    visitsChecked forwardEventChunk146 forwardVisitTree146 = true := by
  decide +kernel

theorem eventVisits_forwardChunk146 (r : Nat) :
    eventVisits r forwardEventChunk146 = fastForwardChunkVisits146 r :=
  eventVisits_of_tree _ _ covered146 checked146 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk146

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 147. -/
def forwardVisitTree147 : VisitTree := (VisitTree.branch 400 (VisitTree.branch 344 (VisitTree.branch 312 (VisitTree.leaf 283 [1, 1, 1]) (VisitTree.branch 325 (VisitTree.leaf 312 [1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 325 [1, 1]))) (VisitTree.branch 359 (VisitTree.branch 355 (VisitTree.leaf 344 [1, 1, 1, 1]) (VisitTree.leaf 355 [1, 1, 1, 1, 1, 1])) (VisitTree.branch 390 (VisitTree.leaf 359 [1, 1]) (VisitTree.leaf 390 [1, 1, 1, 1, 1])))) (VisitTree.branch 434 (VisitTree.branch 418 (VisitTree.branch 412 (VisitTree.leaf 400 [1, 1, 1, 1, 1]) (VisitTree.leaf 412 [1, 1, 1, 1, 1])) (VisitTree.branch 429 (VisitTree.leaf 418 [1, 1, 1]) (VisitTree.leaf 429 [1, 1, 1, 1, 1]))) (VisitTree.branch 490 (VisitTree.branch 442 (VisitTree.leaf 434 [1, 1, 1, 1, 1]) (VisitTree.leaf 442 [1, 1])) (VisitTree.branch 508 (VisitTree.leaf 490 [1, 1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 508 [1, 1])))))

def fastForwardChunkVisits147 (r : Nat) : List Nat :=
  forwardVisitTree147.lookup r

private theorem covered147 :
    visitsCovered forwardEventChunk147 forwardVisitTree147 = true := by
  decide +kernel

private theorem checked147 :
    visitsChecked forwardEventChunk147 forwardVisitTree147 = true := by
  decide +kernel

theorem eventVisits_forwardChunk147 (r : Nat) :
    eventVisits r forwardEventChunk147 = fastForwardChunkVisits147 r :=
  eventVisits_of_tree _ _ covered147 checked147 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk147


