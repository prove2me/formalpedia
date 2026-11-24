-- Prove2me | Definitions.Def_CSL_Generated_MemoryAccess_Group03
-- name    : CSL_Generated_MemoryAccess_Group03
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T13:32:29.755863+00:00
-- url     : https://prove2.me/theorems/5b041ccf-d1df-4e44-a849-d9374a91eb2e
-- title:
--   Coded sorting library: Generated / MemoryAccess / Group03
-- statement:
--   Module `CodedSorting.Generated.MemoryAccess.Group03` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Generated.MemoryAccess.Group03

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Circuit_MemoryAccess_PhysicalFrameEventChunkData
import Definitions.Def_CSL_Generated_MemoryAccess_Base

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 52. -/
def forwardVisitTree052 : VisitTree := (VisitTree.branch 595 (VisitTree.branch 560 (VisitTree.branch 534 (VisitTree.branch 524 (VisitTree.leaf 523 [313, 313, 313, 313, 313, 313, 313, 313]) (VisitTree.leaf 524 [312])) (VisitTree.branch 549 (VisitTree.leaf 534 [314, 314, 314, 314, 314]) (VisitTree.leaf 549 [313, 313, 313, 313, 313]))) (VisitTree.branch 565 (VisitTree.branch 564 (VisitTree.leaf 560 [312, 312]) (VisitTree.leaf 564 [313, 313, 313])) (VisitTree.branch 586 (VisitTree.leaf 565 [314, 314]) (VisitTree.leaf 586 [313, 313, 313, 313, 313])))) (VisitTree.branch 621 (VisitTree.branch 609 (VisitTree.branch 602 (VisitTree.leaf 595 [312]) (VisitTree.leaf 602 [314, 314, 314, 314])) (VisitTree.branch 620 (VisitTree.leaf 609 [312, 312]) (VisitTree.leaf 620 [314, 314, 314]))) (VisitTree.branch 633 (VisitTree.branch 632 (VisitTree.leaf 621 [313, 313, 313, 313, 313, 313]) (VisitTree.leaf 632 [314, 314, 314])) (VisitTree.branch 650 (VisitTree.leaf 633 [313, 313, 313, 313, 313, 313, 313]) (VisitTree.leaf 650 [314, 314, 314, 314, 314, 314, 314])))))

def fastForwardChunkVisits052 (r : Nat) : List Nat :=
  forwardVisitTree052.lookup r

private theorem covered052 :
    visitsCovered forwardEventChunk052 forwardVisitTree052 = true := by
  decide +kernel

private theorem checked052 :
    visitsChecked forwardEventChunk052 forwardVisitTree052 = true := by
  decide +kernel

theorem eventVisits_forwardChunk052 (r : Nat) :
    eventVisits r forwardEventChunk052 = fastForwardChunkVisits052 r :=
  eventVisits_of_tree _ _ covered052 checked052 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk052

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 53. -/
def forwardVisitTree053 : VisitTree := (VisitTree.branch 577 (VisitTree.branch 546 (VisitTree.branch 534 (VisitTree.branch 533 (VisitTree.leaf 532 [316, 316, 316, 316]) (VisitTree.leaf 533 [315, 315, 315, 315, 315, 315, 315, 315])) (VisitTree.branch 535 (VisitTree.leaf 534 [314, 314, 314]) (VisitTree.leaf 535 [315, 315, 315, 315, 315]))) (VisitTree.branch 566 (VisitTree.branch 565 (VisitTree.leaf 546 [316, 316, 316, 316, 316]) (VisitTree.leaf 565 [314, 314, 314])) (VisitTree.branch 567 (VisitTree.leaf 566 [315, 315, 315]) (VisitTree.branch 576 (VisitTree.leaf 567 [316, 316]) (VisitTree.leaf 576 [315, 315, 315, 315, 315]))))) (VisitTree.branch 620 (VisitTree.branch 602 (VisitTree.branch 599 (VisitTree.leaf 577 [316]) (VisitTree.leaf 599 [315, 315, 315, 315, 315, 315])) (VisitTree.branch 614 (VisitTree.leaf 602 [314]) (VisitTree.leaf 614 [316, 316]))) (VisitTree.branch 638 (VisitTree.branch 632 (VisitTree.leaf 620 [314, 314, 314]) (VisitTree.leaf 632 [314, 314, 314])) (VisitTree.branch 650 (VisitTree.leaf 638 [316, 316]) (VisitTree.branch 659 (VisitTree.leaf 650 [314, 314, 314]) (VisitTree.leaf 659 [315, 315, 315, 315, 315]))))))

def fastForwardChunkVisits053 (r : Nat) : List Nat :=
  forwardVisitTree053.lookup r

private theorem covered053 :
    visitsCovered forwardEventChunk053 forwardVisitTree053 = true := by
  decide +kernel

private theorem checked053 :
    visitsChecked forwardEventChunk053 forwardVisitTree053 = true := by
  decide +kernel

theorem eventVisits_forwardChunk053 (r : Nat) :
    eventVisits r forwardEventChunk053 = fastForwardChunkVisits053 r :=
  eventVisits_of_tree _ _ covered053 checked053 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk053

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 54. -/
def forwardVisitTree054 : VisitTree := (VisitTree.branch 568 (VisitTree.branch 540 (VisitTree.branch 531 (VisitTree.leaf 530 [318]) (VisitTree.branch 532 (VisitTree.leaf 531 [317, 317, 317, 317, 317, 317, 317, 317]) (VisitTree.leaf 532 [316, 316, 316, 316]))) (VisitTree.branch 546 (VisitTree.branch 541 (VisitTree.leaf 540 [318]) (VisitTree.leaf 541 [317, 317, 317, 317, 317, 317, 317])) (VisitTree.branch 567 (VisitTree.leaf 546 [316]) (VisitTree.leaf 567 [316, 316, 316])))) (VisitTree.branch 614 (VisitTree.branch 577 (VisitTree.leaf 568 [317, 317, 317, 317, 317, 317, 317]) (VisitTree.branch 582 (VisitTree.leaf 577 [316, 316, 316, 316, 316]) (VisitTree.leaf 582 [317, 317, 317, 317, 317]))) (VisitTree.branch 638 (VisitTree.branch 617 (VisitTree.leaf 614 [316, 316, 316, 316, 316]) (VisitTree.leaf 617 [317, 317, 317, 317, 317, 317])) (VisitTree.branch 641 (VisitTree.leaf 638 [316, 316, 316, 316]) (VisitTree.leaf 641 [317, 317, 317, 317, 317, 317, 317])))))

def fastForwardChunkVisits054 (r : Nat) : List Nat :=
  forwardVisitTree054.lookup r

private theorem covered054 :
    visitsCovered forwardEventChunk054 forwardVisitTree054 = true := by
  decide +kernel

private theorem checked054 :
    visitsChecked forwardEventChunk054 forwardVisitTree054 = true := by
  decide +kernel

theorem eventVisits_forwardChunk054 (r : Nat) :
    eventVisits r forwardEventChunk054 = fastForwardChunkVisits054 r :=
  eventVisits_of_tree _ _ covered054 checked054 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk054

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 55. -/
def forwardVisitTree055 : VisitTree := (VisitTree.branch 596 (VisitTree.branch 569 (VisitTree.branch 530 (VisitTree.leaf 529 [319, 319, 319, 319, 319]) (VisitTree.branch 540 (VisitTree.leaf 530 [318, 318, 318, 318, 318, 318, 318]) (VisitTree.leaf 540 [318, 318, 318, 318]))) (VisitTree.branch 570 (VisitTree.leaf 569 [318, 318, 318, 318, 318]) (VisitTree.branch 571 (VisitTree.leaf 570 [319, 319, 319, 319, 319]) (VisitTree.leaf 571 [318, 318, 318, 318, 318, 318, 318])))) (VisitTree.branch 635 (VisitTree.branch 605 (VisitTree.leaf 596 [318, 318, 318, 318, 318, 318, 318]) (VisitTree.branch 623 (VisitTree.leaf 605 [319, 319, 319, 319]) (VisitTree.leaf 623 [319, 319, 319, 319]))) (VisitTree.branch 653 (VisitTree.leaf 635 [319, 319, 319, 319, 319]) (VisitTree.branch 656 (VisitTree.leaf 653 [319, 319, 319, 319, 319]) (VisitTree.leaf 656 [318, 318, 318, 318, 318, 318])))))

def fastForwardChunkVisits055 (r : Nat) : List Nat :=
  forwardVisitTree055.lookup r

private theorem covered055 :
    visitsCovered forwardEventChunk055 forwardVisitTree055 = true := by
  decide +kernel

private theorem checked055 :
    visitsChecked forwardEventChunk055 forwardVisitTree055 = true := by
  decide +kernel

theorem eventVisits_forwardChunk055 (r : Nat) :
    eventVisits r forwardEventChunk055 = fastForwardChunkVisits055 r :=
  eventVisits_of_tree _ _ covered055 checked055 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk055

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 56. -/
def forwardVisitTree056 : VisitTree := (VisitTree.branch 619 (VisitTree.branch 574 (VisitTree.branch 538 (VisitTree.branch 537 (VisitTree.leaf 529 [319, 319]) (VisitTree.leaf 537 [321, 321, 321, 321])) (VisitTree.branch 573 (VisitTree.leaf 538 [320, 320, 320, 320, 320, 320, 320, 320]) (VisitTree.leaf 573 [321, 321]))) (VisitTree.branch 593 (VisitTree.branch 590 (VisitTree.leaf 574 [320, 320, 320, 320, 320, 320, 320, 320]) (VisitTree.leaf 590 [321, 321])) (VisitTree.branch 605 (VisitTree.leaf 593 [320, 320, 320, 320, 320, 320, 320]) (VisitTree.leaf 605 [319, 319, 319])))) (VisitTree.branch 635 (VisitTree.branch 624 (VisitTree.branch 623 (VisitTree.leaf 619 [321, 321]) (VisitTree.leaf 623 [319, 319])) (VisitTree.branch 631 (VisitTree.leaf 624 [320, 320, 320, 320, 320, 320]) (VisitTree.leaf 631 [320, 320, 320, 320, 320, 320]))) (VisitTree.branch 644 (VisitTree.branch 636 (VisitTree.leaf 635 [319, 319]) (VisitTree.leaf 636 [321])) (VisitTree.branch 647 (VisitTree.leaf 644 [320, 320, 320, 320, 320, 320, 320]) (VisitTree.branch 653 (VisitTree.leaf 647 [321]) (VisitTree.leaf 653 [319]))))))

def fastForwardChunkVisits056 (r : Nat) : List Nat :=
  forwardVisitTree056.lookup r

private theorem covered056 :
    visitsCovered forwardEventChunk056 forwardVisitTree056 = true := by
  decide +kernel

private theorem checked056 :
    visitsChecked forwardEventChunk056 forwardVisitTree056 = true := by
  decide +kernel

theorem eventVisits_forwardChunk056 (r : Nat) :
    eventVisits r forwardEventChunk056 = fastForwardChunkVisits056 r :=
  eventVisits_of_tree _ _ covered056 checked056 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk056

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 57. -/
def forwardVisitTree057 : VisitTree := (VisitTree.branch 611 (VisitTree.branch 581 (VisitTree.branch 545 (VisitTree.leaf 537 [321, 321, 321, 321]) (VisitTree.branch 573 (VisitTree.leaf 545 [322, 322, 322, 322, 322]) (VisitTree.leaf 573 [321, 321, 321, 321, 321, 321]))) (VisitTree.branch 590 (VisitTree.leaf 581 [322, 322, 322, 322, 322]) (VisitTree.branch 601 (VisitTree.leaf 590 [321, 321, 321, 321, 321]) (VisitTree.leaf 601 [322, 322, 322, 322, 322, 322])))) (VisitTree.branch 636 (VisitTree.branch 619 (VisitTree.leaf 611 [322, 322, 322, 322, 322]) (VisitTree.branch 626 (VisitTree.leaf 619 [321, 321, 321, 321, 321]) (VisitTree.leaf 626 [322, 322, 322, 322]))) (VisitTree.branch 647 (VisitTree.leaf 636 [321, 321, 321, 321, 321, 321]) (VisitTree.branch 654 (VisitTree.leaf 647 [321, 321, 321, 321, 321, 321]) (VisitTree.leaf 654 [322, 322, 322, 322, 322, 322, 322])))))

def fastForwardChunkVisits057 (r : Nat) : List Nat :=
  forwardVisitTree057.lookup r

private theorem covered057 :
    visitsCovered forwardEventChunk057 forwardVisitTree057 = true := by
  decide +kernel

private theorem checked057 :
    visitsChecked forwardEventChunk057 forwardVisitTree057 = true := by
  decide +kernel

theorem eventVisits_forwardChunk057 (r : Nat) :
    eventVisits r forwardEventChunk057 = fastForwardChunkVisits057 r :=
  eventVisits_of_tree _ _ covered057 checked057 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk057

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 58. -/
def forwardVisitTree058 : VisitTree := (VisitTree.branch 611 (VisitTree.branch 583 (VisitTree.branch 552 (VisitTree.branch 545 (VisitTree.leaf 542 [323, 323, 323, 323, 323, 323, 323, 323]) (VisitTree.leaf 545 [322, 322])) (VisitTree.branch 578 (VisitTree.leaf 552 [324, 324, 324, 324]) (VisitTree.leaf 578 [323, 323, 323, 323, 323]))) (VisitTree.branch 606 (VisitTree.branch 598 (VisitTree.leaf 583 [324, 324, 324, 324, 324]) (VisitTree.leaf 598 [324, 324, 324, 324])) (VisitTree.branch 608 (VisitTree.leaf 606 [323, 323, 323, 323, 323, 323, 323]) (VisitTree.leaf 608 [323, 323, 323, 323, 323, 323])))) (VisitTree.branch 640 (VisitTree.branch 626 (VisitTree.branch 616 (VisitTree.leaf 611 [322]) (VisitTree.leaf 616 [324, 324, 324])) (VisitTree.branch 629 (VisitTree.leaf 626 [322, 322]) (VisitTree.leaf 629 [323, 323, 323, 323, 323, 323]))) (VisitTree.branch 654 (VisitTree.branch 649 (VisitTree.leaf 640 [324, 324, 324]) (VisitTree.leaf 649 [323, 323, 323, 323, 323, 323])) (VisitTree.branch 658 (VisitTree.leaf 654 [322]) (VisitTree.leaf 658 [324])))))

def fastForwardChunkVisits058 (r : Nat) : List Nat :=
  forwardVisitTree058.lookup r

private theorem covered058 :
    visitsCovered forwardEventChunk058 forwardVisitTree058 = true := by
  decide +kernel

private theorem checked058 :
    visitsChecked forwardEventChunk058 forwardVisitTree058 = true := by
  decide +kernel

theorem eventVisits_forwardChunk058 (r : Nat) :
    eventVisits r forwardEventChunk058 = fastForwardChunkVisits058 r :=
  eventVisits_of_tree _ _ covered058 checked058 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk058

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 59. -/
def forwardVisitTree059 : VisitTree := (VisitTree.branch 588 (VisitTree.branch 403 (VisitTree.branch 247 (VisitTree.branch 235 (VisitTree.leaf 234 [328]) (VisitTree.leaf 235 [327])) (VisitTree.branch 351 (VisitTree.leaf 247 [326]) (VisitTree.leaf 351 [326]))) (VisitTree.branch 547 (VisitTree.branch 484 (VisitTree.leaf 403 [327]) (VisitTree.leaf 484 [328])) (VisitTree.branch 552 (VisitTree.leaf 547 [325, 325, 325, 325, 325, 325, 325, 325]) (VisitTree.leaf 552 [324, 324, 324])))) (VisitTree.branch 616 (VisitTree.branch 598 (VisitTree.branch 597 (VisitTree.leaf 588 [325, 325, 325, 325, 325]) (VisitTree.leaf 597 [325, 325, 325, 325, 325])) (VisitTree.branch 615 (VisitTree.leaf 598 [324, 324]) (VisitTree.leaf 615 [325, 325, 325, 325, 325, 325, 325]))) (VisitTree.branch 640 (VisitTree.branch 639 (VisitTree.leaf 616 [324, 324, 324, 324]) (VisitTree.leaf 639 [325, 325, 325, 325, 325, 325])) (VisitTree.branch 657 (VisitTree.leaf 640 [324, 324, 324]) (VisitTree.branch 658 (VisitTree.leaf 657 [325, 325, 325, 325, 325, 325, 325, 325, 325]) (VisitTree.leaf 658 [324, 324, 324, 324, 324, 324]))))))

def fastForwardChunkVisits059 (r : Nat) : List Nat :=
  forwardVisitTree059.lookup r

private theorem covered059 :
    visitsCovered forwardEventChunk059 forwardVisitTree059 = true := by
  decide +kernel

private theorem checked059 :
    visitsChecked forwardEventChunk059 forwardVisitTree059 = true := by
  decide +kernel

theorem eventVisits_forwardChunk059 (r : Nat) :
    eventVisits r forwardEventChunk059 = fastForwardChunkVisits059 r :=
  eventVisits_of_tree _ _ covered059 checked059 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk059

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 60. -/
def forwardVisitTree060 : VisitTree := (VisitTree.branch 387 (VisitTree.branch 325 (VisitTree.branch 291 (VisitTree.branch 246 (VisitTree.branch 242 (VisitTree.branch 240 (VisitTree.leaf 223 [348]) (VisitTree.leaf 240 [330])) (VisitTree.branch 243 (VisitTree.leaf 242 [347]) (VisitTree.leaf 243 [344]))) (VisitTree.branch 264 (VisitTree.branch 256 (VisitTree.leaf 246 [346]) (VisitTree.leaf 256 [334])) (VisitTree.branch 272 (VisitTree.leaf 264 [360]) (VisitTree.leaf 272 [347])))) (VisitTree.branch 312 (VisitTree.branch 308 (VisitTree.branch 305 (VisitTree.leaf 291 [341]) (VisitTree.leaf 305 [351])) (VisitTree.branch 310 (VisitTree.leaf 308 [348]) (VisitTree.leaf 310 [333]))) (VisitTree.branch 323 (VisitTree.branch 321 (VisitTree.leaf 312 [353]) (VisitTree.leaf 321 [357])) (VisitTree.branch 324 (VisitTree.leaf 323 [339]) (VisitTree.leaf 324 [355]))))) (VisitTree.branch 347 (VisitTree.branch 338 (VisitTree.branch 329 (VisitTree.branch 326 (VisitTree.leaf 325 [352]) (VisitTree.leaf 326 [337])) (VisitTree.branch 336 (VisitTree.leaf 329 [332]) (VisitTree.leaf 336 [358]))) (VisitTree.branch 344 (VisitTree.branch 341 (VisitTree.leaf 338 [344]) (VisitTree.leaf 341 [350])) (VisitTree.branch 345 (VisitTree.leaf 344 [352]) (VisitTree.leaf 345 [333])))) (VisitTree.branch 372 (VisitTree.branch 364 (VisitTree.branch 354 (VisitTree.leaf 347 [356]) (VisitTree.leaf 354 [355])) (VisitTree.branch 366 (VisitTree.leaf 364 [350]) (VisitTree.leaf 366 [339]))) (VisitTree.branch 375 (VisitTree.branch 373 (VisitTree.leaf 372 [340]) (VisitTree.leaf 373 [338])) (VisitTree.branch 380 (VisitTree.leaf 375 [332]) (VisitTree.leaf 380 [351])))))) (VisitTree.branch 493 (VisitTree.branch 455 (VisitTree.branch 417 (VisitTree.branch 402 (VisitTree.branch 400 (VisitTree.leaf 387 [357]) (VisitTree.leaf 400 [335])) (VisitTree.branch 409 (VisitTree.leaf 402 [342]) (VisitTree.leaf 409 [340]))) (VisitTree.branch 430 (VisitTree.branch 421 (VisitTree.leaf 417 [330]) (VisitTree.leaf 421 [346])) (VisitTree.branch 432 (VisitTree.leaf 430 [341]) (VisitTree.leaf 432 [342])))) (VisitTree.branch 488 (VisitTree.branch 485 (VisitTree.branch 483 (VisitTree.leaf 455 [349]) (VisitTree.leaf 483 [329])) (VisitTree.branch 486 (VisitTree.leaf 485 [345]) (VisitTree.leaf 486 [349]))) (VisitTree.branch 490 (VisitTree.branch 489 (VisitTree.leaf 488 [336]) (VisitTree.leaf 489 [353])) (VisitTree.branch 491 (VisitTree.leaf 490 [334]) (VisitTree.leaf 491 [354]))))) (VisitTree.branch 504 (VisitTree.branch 498 (VisitTree.branch 495 (VisitTree.branch 494 (VisitTree.leaf 493 [343]) (VisitTree.leaf 494 [360])) (VisitTree.branch 496 (VisitTree.leaf 495 [359]) (VisitTree.leaf 496 [359]))) (VisitTree.branch 501 (VisitTree.branch 499 (VisitTree.leaf 498 [338]) (VisitTree.leaf 499 [331])) (VisitTree.branch 503 (VisitTree.leaf 501 [329]) (VisitTree.leaf 503 [345])))) (VisitTree.branch 510 (VisitTree.branch 507 (VisitTree.branch 506 (VisitTree.leaf 504 [331]) (VisitTree.leaf 506 [354])) (VisitTree.branch 509 (VisitTree.leaf 507 [335]) (VisitTree.leaf 509 [336]))) (VisitTree.branch 514 (VisitTree.branch 511 (VisitTree.leaf 510 [337]) (VisitTree.leaf 511 [343])) (VisitTree.branch 516 (VisitTree.leaf 514 [358]) (VisitTree.leaf 516 [356])))))))

def fastForwardChunkVisits060 (r : Nat) : List Nat :=
  forwardVisitTree060.lookup r

private theorem covered060 :
    visitsCovered forwardEventChunk060 forwardVisitTree060 = true := by
  decide +kernel

private theorem checked060 :
    visitsChecked forwardEventChunk060 forwardVisitTree060 = true := by
  decide +kernel

theorem eventVisits_forwardChunk060 (r : Nat) :
    eventVisits r forwardEventChunk060 = fastForwardChunkVisits060 r :=
  eventVisits_of_tree _ _ covered060 checked060 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk060

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 61. -/
def forwardVisitTree061 : VisitTree := (VisitTree.branch 515 (VisitTree.branch 359 (VisitTree.branch 286 (VisitTree.branch 253 (VisitTree.branch 251 (VisitTree.branch 232 (VisitTree.leaf 222 [374]) (VisitTree.leaf 232 [379])) (VisitTree.branch 252 (VisitTree.leaf 251 [377]) (VisitTree.leaf 252 [367]))) (VisitTree.branch 274 (VisitTree.branch 265 (VisitTree.leaf 253 [368]) (VisitTree.leaf 265 [372])) (VisitTree.branch 281 (VisitTree.leaf 274 [385]) (VisitTree.leaf 281 [382])))) (VisitTree.branch 320 (VisitTree.branch 309 (VisitTree.branch 296 (VisitTree.leaf 286 [383]) (VisitTree.leaf 296 [391])) (VisitTree.branch 313 (VisitTree.leaf 309 [369]) (VisitTree.leaf 313 [364]))) (VisitTree.branch 355 (VisitTree.branch 348 (VisitTree.leaf 320 [361]) (VisitTree.leaf 348 [365])) (VisitTree.branch 356 (VisitTree.leaf 355 [388]) (VisitTree.leaf 356 [361]))))) (VisitTree.branch 456 (VisitTree.branch 384 (VisitTree.branch 363 (VisitTree.branch 361 (VisitTree.leaf 359 [366]) (VisitTree.leaf 361 [370])) (VisitTree.branch 369 (VisitTree.leaf 363 [376]) (VisitTree.leaf 369 [392]))) (VisitTree.branch 420 (VisitTree.branch 405 (VisitTree.leaf 384 [390]) (VisitTree.leaf 405 [386])) (VisitTree.branch 426 (VisitTree.leaf 420 [387]) (VisitTree.leaf 426 [363])))) (VisitTree.branch 502 (VisitTree.branch 497 (VisitTree.branch 482 (VisitTree.leaf 456 [375]) (VisitTree.leaf 482 [380])) (VisitTree.branch 500 (VisitTree.leaf 497 [384]) (VisitTree.leaf 500 [373]))) (VisitTree.branch 508 (VisitTree.branch 505 (VisitTree.leaf 502 [362]) (VisitTree.leaf 505 [378])) (VisitTree.branch 512 (VisitTree.leaf 508 [389]) (VisitTree.leaf 512 [371])))))) (VisitTree.branch 543 (VisitTree.branch 531 (VisitTree.branch 521 (VisitTree.branch 518 (VisitTree.branch 517 (VisitTree.leaf 515 [381]) (VisitTree.leaf 517 [367])) (VisitTree.branch 520 (VisitTree.leaf 518 [384]) (VisitTree.leaf 520 [364]))) (VisitTree.branch 526 (VisitTree.branch 525 (VisitTree.leaf 521 [381]) (VisitTree.leaf 525 [371])) (VisitTree.branch 530 (VisitTree.leaf 526 [389]) (VisitTree.leaf 530 [378])))) (VisitTree.branch 535 (VisitTree.branch 533 (VisitTree.branch 532 (VisitTree.leaf 531 [391]) (VisitTree.leaf 532 [386])) (VisitTree.branch 534 (VisitTree.leaf 533 [385]) (VisitTree.leaf 534 [374]))) (VisitTree.branch 539 (VisitTree.branch 536 (VisitTree.leaf 535 [375]) (VisitTree.leaf 536 [366])) (VisitTree.branch 541 (VisitTree.leaf 539 [363]) (VisitTree.leaf 541 [377]))))) (VisitTree.branch 570 (VisitTree.branch 550 (VisitTree.branch 548 (VisitTree.branch 546 (VisitTree.leaf 543 [370]) (VisitTree.leaf 546 [376])) (VisitTree.branch 549 (VisitTree.leaf 548 [362]) (VisitTree.leaf 549 [373]))) (VisitTree.branch 561 (VisitTree.branch 555 (VisitTree.leaf 550 [368]) (VisitTree.leaf 555 [365])) (VisitTree.branch 569 (VisitTree.leaf 561 [388]) (VisitTree.leaf 569 [380])))) (VisitTree.branch 598 (VisitTree.branch 574 (VisitTree.branch 573 (VisitTree.leaf 570 [379]) (VisitTree.leaf 573 [383])) (VisitTree.branch 595 (VisitTree.leaf 574 [382]) (VisitTree.leaf 595 [372]))) (VisitTree.branch 601 (VisitTree.branch 600 (VisitTree.leaf 598 [392]) (VisitTree.leaf 600 [369])) (VisitTree.branch 606 (VisitTree.leaf 601 [387]) (VisitTree.leaf 606 [390])))))))

def fastForwardChunkVisits061 (r : Nat) : List Nat :=
  forwardVisitTree061.lookup r

private theorem covered061 :
    visitsCovered forwardEventChunk061 forwardVisitTree061 = true := by
  decide +kernel

private theorem checked061 :
    visitsChecked forwardEventChunk061 forwardVisitTree061 = true := by
  decide +kernel

theorem eventVisits_forwardChunk061 (r : Nat) :
    eventVisits r forwardEventChunk061 = fastForwardChunkVisits061 r :=
  eventVisits_of_tree _ _ covered061 checked061 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk061

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 62. -/
def forwardVisitTree062 : VisitTree := (VisitTree.branch 519 (VisitTree.branch 362 (VisitTree.branch 298 (VisitTree.branch 270 (VisitTree.branch 268 (VisitTree.branch 261 (VisitTree.leaf 225 [396]) (VisitTree.leaf 261 [408])) (VisitTree.branch 269 (VisitTree.leaf 268 [403]) (VisitTree.leaf 269 [401]))) (VisitTree.branch 280 (VisitTree.branch 279 (VisitTree.leaf 270 [418]) (VisitTree.leaf 279 [400])) (VisitTree.branch 285 (VisitTree.leaf 280 [421]) (VisitTree.leaf 285 [407])))) (VisitTree.branch 337 (VisitTree.branch 303 (VisitTree.branch 299 (VisitTree.leaf 298 [409]) (VisitTree.leaf 299 [419])) (VisitTree.branch 315 (VisitTree.leaf 303 [423]) (VisitTree.leaf 315 [405]))) (VisitTree.branch 343 (VisitTree.branch 342 (VisitTree.leaf 337 [393]) (VisitTree.leaf 342 [397])) (VisitTree.branch 346 (VisitTree.leaf 343 [411]) (VisitTree.leaf 346 [415]))))) (VisitTree.branch 427 (VisitTree.branch 389 (VisitTree.branch 379 (VisitTree.branch 378 (VisitTree.leaf 362 [414]) (VisitTree.leaf 378 [413])) (VisitTree.branch 388 (VisitTree.leaf 379 [410]) (VisitTree.leaf 388 [420]))) (VisitTree.branch 395 (VisitTree.branch 390 (VisitTree.leaf 389 [404]) (VisitTree.leaf 390 [424])) (VisitTree.branch 401 (VisitTree.leaf 395 [417]) (VisitTree.leaf 401 [422])))) (VisitTree.branch 442 (VisitTree.branch 437 (VisitTree.branch 431 (VisitTree.leaf 427 [398]) (VisitTree.leaf 431 [402])) (VisitTree.branch 440 (VisitTree.leaf 437 [416]) (VisitTree.leaf 440 [406]))) (VisitTree.branch 487 (VisitTree.branch 448 (VisitTree.leaf 442 [399]) (VisitTree.leaf 448 [412])) (VisitTree.branch 492 (VisitTree.leaf 487 [394]) (VisitTree.leaf 492 [395])))))) (VisitTree.branch 563 (VisitTree.branch 544 (VisitTree.branch 528 (VisitTree.branch 523 (VisitTree.branch 522 (VisitTree.leaf 519 [401]) (VisitTree.leaf 522 [396])) (VisitTree.branch 524 (VisitTree.leaf 523 [395]) (VisitTree.leaf 524 [408]))) (VisitTree.branch 538 (VisitTree.branch 537 (VisitTree.leaf 528 [394]) (VisitTree.leaf 537 [419])) (VisitTree.branch 540 (VisitTree.leaf 538 [418]) (VisitTree.leaf 540 [411])))) (VisitTree.branch 556 (VisitTree.branch 553 (VisitTree.branch 551 (VisitTree.leaf 544 [407]) (VisitTree.leaf 551 [393])) (VisitTree.branch 554 (VisitTree.leaf 553 [403]) (VisitTree.leaf 554 [420]))) (VisitTree.branch 559 (VisitTree.branch 557 (VisitTree.leaf 556 [400]) (VisitTree.leaf 557 [399])) (VisitTree.branch 562 (VisitTree.leaf 559 [409]) (VisitTree.leaf 562 [406]))))) (VisitTree.branch 596 (VisitTree.branch 581 (VisitTree.branch 566 (VisitTree.branch 564 (VisitTree.leaf 563 [405]) (VisitTree.leaf 564 [404])) (VisitTree.branch 567 (VisitTree.leaf 566 [414]) (VisitTree.leaf 567 [413]))) (VisitTree.branch 584 (VisitTree.branch 582 (VisitTree.leaf 581 [423]) (VisitTree.leaf 582 [422])) (VisitTree.branch 594 (VisitTree.leaf 584 [398]) (VisitTree.leaf 594 [424])))) (VisitTree.branch 605 (VisitTree.branch 599 (VisitTree.branch 597 (VisitTree.leaf 596 [421]) (VisitTree.leaf 597 [397])) (VisitTree.branch 602 (VisitTree.leaf 599 [416]) (VisitTree.leaf 602 [415]))) (VisitTree.branch 612 (VisitTree.branch 607 (VisitTree.leaf 605 [410]) (VisitTree.leaf 607 [417])) (VisitTree.branch 617 (VisitTree.leaf 612 [402]) (VisitTree.leaf 617 [412])))))))

def fastForwardChunkVisits062 (r : Nat) : List Nat :=
  forwardVisitTree062.lookup r

private theorem covered062 :
    visitsCovered forwardEventChunk062 forwardVisitTree062 = true := by
  decide +kernel

private theorem checked062 :
    visitsChecked forwardEventChunk062 forwardVisitTree062 = true := by
  decide +kernel

theorem eventVisits_forwardChunk062 (r : Nat) :
    eventVisits r forwardEventChunk062 = fastForwardChunkVisits062 r :=
  eventVisits_of_tree _ _ covered062 checked062 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk062

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 63. -/
def forwardVisitTree063 : VisitTree := (VisitTree.branch 527 (VisitTree.branch 370 (VisitTree.branch 330 (VisitTree.branch 302 (VisitTree.branch 292 (VisitTree.branch 249 (VisitTree.leaf 244 [439]) (VisitTree.leaf 249 [436])) (VisitTree.branch 294 (VisitTree.leaf 292 [426]) (VisitTree.leaf 294 [427]))) (VisitTree.branch 318 (VisitTree.branch 304 (VisitTree.leaf 302 [445]) (VisitTree.leaf 304 [451])) (VisitTree.branch 328 (VisitTree.leaf 318 [449]) (VisitTree.leaf 328 [432])))) (VisitTree.branch 339 (VisitTree.branch 334 (VisitTree.branch 331 (VisitTree.leaf 330 [455]) (VisitTree.leaf 331 [431])) (VisitTree.branch 335 (VisitTree.leaf 334 [433]) (VisitTree.leaf 335 [437]))) (VisitTree.branch 353 (VisitTree.branch 350 (VisitTree.leaf 339 [453]) (VisitTree.leaf 350 [438])) (VisitTree.branch 367 (VisitTree.leaf 353 [428]) (VisitTree.leaf 367 [441]))))) (VisitTree.branch 422 (VisitTree.branch 391 (VisitTree.branch 376 (VisitTree.branch 374 (VisitTree.leaf 370 [454]) (VisitTree.leaf 374 [448])) (VisitTree.branch 383 (VisitTree.leaf 376 [435]) (VisitTree.leaf 383 [443]))) (VisitTree.branch 397 (VisitTree.branch 392 (VisitTree.leaf 391 [440]) (VisitTree.leaf 392 [442])) (VisitTree.branch 412 (VisitTree.leaf 397 [446]) (VisitTree.leaf 412 [425])))) (VisitTree.branch 454 (VisitTree.branch 446 (VisitTree.branch 445 (VisitTree.leaf 422 [450]) (VisitTree.leaf 445 [447])) (VisitTree.branch 453 (VisitTree.leaf 446 [456]) (VisitTree.leaf 453 [429]))) (VisitTree.branch 481 (VisitTree.branch 457 (VisitTree.leaf 454 [430]) (VisitTree.leaf 457 [452])) (VisitTree.branch 513 (VisitTree.leaf 481 [434]) (VisitTree.leaf 513 [444])))))) (VisitTree.branch 585 (VisitTree.branch 565 (VisitTree.branch 547 (VisitTree.branch 542 (VisitTree.branch 529 (VisitTree.leaf 527 [440]) (VisitTree.leaf 529 [447])) (VisitTree.branch 545 (VisitTree.leaf 542 [426]) (VisitTree.leaf 545 [451]))) (VisitTree.branch 558 (VisitTree.branch 552 (VisitTree.leaf 547 [428]) (VisitTree.leaf 552 [442])) (VisitTree.branch 560 (VisitTree.leaf 558 [432]) (VisitTree.leaf 560 [445])))) (VisitTree.branch 578 (VisitTree.branch 572 (VisitTree.branch 571 (VisitTree.leaf 565 [450]) (VisitTree.leaf 571 [444])) (VisitTree.branch 576 (VisitTree.leaf 572 [452]) (VisitTree.leaf 576 [441]))) (VisitTree.branch 580 (VisitTree.branch 579 (VisitTree.leaf 578 [446]) (VisitTree.leaf 579 [439])) (VisitTree.branch 583 (VisitTree.leaf 580 [434]) (VisitTree.leaf 583 [433]))))) (VisitTree.branch 614 (VisitTree.branch 603 (VisitTree.branch 588 (VisitTree.branch 587 (VisitTree.leaf 585 [431]) (VisitTree.leaf 587 [429])) (VisitTree.branch 589 (VisitTree.leaf 588 [443]) (VisitTree.leaf 589 [425]))) (VisitTree.branch 608 (VisitTree.branch 604 (VisitTree.leaf 603 [449]) (VisitTree.leaf 604 [448])) (VisitTree.branch 613 (VisitTree.leaf 608 [456]) (VisitTree.leaf 613 [436])))) (VisitTree.branch 624 (VisitTree.branch 619 (VisitTree.branch 618 (VisitTree.leaf 614 [427]) (VisitTree.leaf 618 [437])) (VisitTree.branch 621 (VisitTree.leaf 619 [438]) (VisitTree.leaf 621 [430]))) (VisitTree.branch 627 (VisitTree.branch 626 (VisitTree.leaf 624 [435]) (VisitTree.leaf 626 [453])) (VisitTree.branch 660 (VisitTree.leaf 627 [454]) (VisitTree.leaf 660 [455])))))))

def fastForwardChunkVisits063 (r : Nat) : List Nat :=
  forwardVisitTree063.lookup r

private theorem covered063 :
    visitsCovered forwardEventChunk063 forwardVisitTree063 = true := by
  decide +kernel

private theorem checked063 :
    visitsChecked forwardEventChunk063 forwardVisitTree063 = true := by
  decide +kernel

theorem eventVisits_forwardChunk063 (r : Nat) :
    eventVisits r forwardEventChunk063 = fastForwardChunkVisits063 r :=
  eventVisits_of_tree _ _ covered063 checked063 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk063

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 64. -/
def forwardVisitTree064 : VisitTree := (VisitTree.branch 568 (VisitTree.branch 306 (VisitTree.branch 262 (VisitTree.branch 236 (VisitTree.branch 230 (VisitTree.branch 226 (VisitTree.leaf 224 [474]) (VisitTree.leaf 226 [475])) (VisitTree.branch 231 (VisitTree.leaf 230 [472]) (VisitTree.leaf 231 [471]))) (VisitTree.branch 258 (VisitTree.branch 255 (VisitTree.leaf 236 [457]) (VisitTree.leaf 255 [466])) (VisitTree.branch 260 (VisitTree.leaf 258 [487]) (VisitTree.leaf 260 [463])))) (VisitTree.branch 275 (VisitTree.branch 266 (VisitTree.branch 263 (VisitTree.leaf 262 [484]) (VisitTree.leaf 263 [483])) (VisitTree.branch 267 (VisitTree.leaf 266 [469]) (VisitTree.leaf 267 [478]))) (VisitTree.branch 283 (VisitTree.branch 276 (VisitTree.leaf 275 [462]) (VisitTree.leaf 276 [481])) (VisitTree.branch 300 (VisitTree.leaf 283 [465]) (VisitTree.leaf 300 [486]))))) (VisitTree.branch 429 (VisitTree.branch 419 (VisitTree.branch 406 (VisitTree.branch 314 (VisitTree.leaf 306 [479]) (VisitTree.leaf 314 [461])) (VisitTree.branch 418 (VisitTree.leaf 406 [460]) (VisitTree.leaf 418 [480]))) (VisitTree.branch 424 (VisitTree.branch 423 (VisitTree.leaf 419 [464]) (VisitTree.leaf 423 [458])) (VisitTree.branch 425 (VisitTree.leaf 424 [485]) (VisitTree.leaf 425 [482])))) (VisitTree.branch 441 (VisitTree.branch 438 (VisitTree.branch 434 (VisitTree.leaf 429 [477]) (VisitTree.leaf 434 [468])) (VisitTree.branch 439 (VisitTree.leaf 438 [467]) (VisitTree.leaf 439 [476]))) (VisitTree.branch 458 (VisitTree.branch 447 (VisitTree.leaf 441 [459]) (VisitTree.leaf 447 [470])) (VisitTree.branch 461 (VisitTree.leaf 458 [473]) (VisitTree.leaf 461 [488])))))) (VisitTree.branch 630 (VisitTree.branch 609 (VisitTree.branch 590 (VisitTree.branch 577 (VisitTree.branch 575 (VisitTree.leaf 568 [459]) (VisitTree.leaf 575 [457])) (VisitTree.branch 586 (VisitTree.leaf 577 [462]) (VisitTree.leaf 586 [467]))) (VisitTree.branch 592 (VisitTree.branch 591 (VisitTree.leaf 590 [469]) (VisitTree.leaf 591 [458])) (VisitTree.branch 593 (VisitTree.leaf 592 [463]) (VisitTree.leaf 593 [464])))) (VisitTree.branch 620 (VisitTree.branch 615 (VisitTree.branch 611 (VisitTree.leaf 609 [472]) (VisitTree.leaf 611 [474])) (VisitTree.branch 616 (VisitTree.leaf 615 [461]) (VisitTree.leaf 616 [460]))) (VisitTree.branch 625 (VisitTree.branch 622 (VisitTree.leaf 620 [468]) (VisitTree.leaf 622 [478])) (VisitTree.branch 629 (VisitTree.leaf 625 [475]) (VisitTree.leaf 629 [471]))))) (VisitTree.branch 638 (VisitTree.branch 634 (VisitTree.branch 632 (VisitTree.branch 631 (VisitTree.leaf 630 [470]) (VisitTree.leaf 631 [481])) (VisitTree.branch 633 (VisitTree.leaf 632 [480]) (VisitTree.leaf 633 [479]))) (VisitTree.branch 636 (VisitTree.branch 635 (VisitTree.leaf 634 [466]) (VisitTree.leaf 635 [465])) (VisitTree.branch 637 (VisitTree.leaf 636 [476]) (VisitTree.leaf 637 [487])))) (VisitTree.branch 642 (VisitTree.branch 640 (VisitTree.branch 639 (VisitTree.leaf 638 [486]) (VisitTree.leaf 639 [485])) (VisitTree.branch 641 (VisitTree.leaf 640 [484]) (VisitTree.leaf 641 [483]))) (VisitTree.branch 653 (VisitTree.branch 648 (VisitTree.leaf 642 [482]) (VisitTree.leaf 648 [488])) (VisitTree.branch 655 (VisitTree.leaf 653 [477]) (VisitTree.leaf 655 [473])))))))

def fastForwardChunkVisits064 (r : Nat) : List Nat :=
  forwardVisitTree064.lookup r

private theorem covered064 :
    visitsCovered forwardEventChunk064 forwardVisitTree064 = true := by
  decide +kernel

private theorem checked064 :
    visitsChecked forwardEventChunk064 forwardVisitTree064 = true := by
  decide +kernel

theorem eventVisits_forwardChunk064 (r : Nat) :
    eventVisits r forwardEventChunk064 = fastForwardChunkVisits064 r :=
  eventVisits_of_tree _ _ covered064 checked064 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk064

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 65. -/
def forwardVisitTree065 : VisitTree := (VisitTree.branch 408 (VisitTree.branch 293 (VisitTree.branch 228 (VisitTree.branch 57 (VisitTree.branch 17 (VisitTree.branch 11 (VisitTree.leaf 6 [506, 506]) (VisitTree.leaf 11 [507])) (VisitTree.branch 43 (VisitTree.leaf 17 [509, 509]) (VisitTree.branch 56 (VisitTree.leaf 43 [508]) (VisitTree.leaf 56 [506, 506])))) (VisitTree.branch 69 (VisitTree.branch 68 (VisitTree.leaf 57 [508]) (VisitTree.leaf 68 [507])) (VisitTree.branch 223 (VisitTree.leaf 69 [507, 507]) (VisitTree.branch 227 (VisitTree.leaf 223 [348]) (VisitTree.leaf 227 [456]))))) (VisitTree.branch 241 (VisitTree.branch 238 (VisitTree.branch 233 (VisitTree.leaf 228 [507, 330]) (VisitTree.leaf 233 [506, 506, 506])) (VisitTree.branch 239 (VisitTree.leaf 238 [493]) (VisitTree.branch 240 (VisitTree.leaf 239 [491]) (VisitTree.leaf 240 [330])))) (VisitTree.branch 282 (VisitTree.branch 271 (VisitTree.leaf 241 [506, 506]) (VisitTree.leaf 271 [509, 509])) (VisitTree.branch 288 (VisitTree.leaf 282 [504]) (VisitTree.branch 289 (VisitTree.leaf 288 [499]) (VisitTree.leaf 289 [498])))))) (VisitTree.branch 357 (VisitTree.branch 319 (VisitTree.branch 301 (VisitTree.branch 297 (VisitTree.leaf 293 [509, 509]) (VisitTree.leaf 297 [508])) (VisitTree.branch 316 (VisitTree.leaf 301 [495]) (VisitTree.branch 317 (VisitTree.leaf 316 [505]) (VisitTree.leaf 317 [501])))) (VisitTree.branch 340 (VisitTree.branch 322 (VisitTree.leaf 319 [506, 506, 506]) (VisitTree.leaf 322 [506, 506])) (VisitTree.branch 349 (VisitTree.leaf 340 [506, 506]) (VisitTree.branch 352 (VisitTree.leaf 349 [506, 506, 348]) (VisitTree.leaf 352 [509, 509]))))) (VisitTree.branch 371 (VisitTree.branch 360 (VisitTree.branch 358 (VisitTree.leaf 357 [507]) (VisitTree.leaf 358 [507, 507])) (VisitTree.branch 365 (VisitTree.leaf 360 [507, 507]) (VisitTree.branch 368 (VisitTree.leaf 365 [508]) (VisitTree.leaf 368 [508])))) (VisitTree.branch 393 (VisitTree.branch 381 (VisitTree.leaf 371 [509]) (VisitTree.branch 385 (VisitTree.leaf 381 [507, 507]) (VisitTree.leaf 385 [508, 508]))) (VisitTree.branch 399 (VisitTree.leaf 393 [500]) (VisitTree.branch 404 (VisitTree.leaf 399 [494]) (VisitTree.leaf 404 [503]))))))) (VisitTree.branch 470 (VisitTree.branch 449 (VisitTree.branch 416 (VisitTree.branch 413 (VisitTree.branch 410 (VisitTree.leaf 408 [502]) (VisitTree.leaf 410 [497])) (VisitTree.branch 414 (VisitTree.leaf 413 [509, 509]) (VisitTree.branch 415 (VisitTree.leaf 414 [496]) (VisitTree.leaf 415 [455])))) (VisitTree.branch 436 (VisitTree.branch 433 (VisitTree.leaf 416 [508]) (VisitTree.leaf 433 [508, 508])) (VisitTree.branch 444 (VisitTree.leaf 436 [470]) (VisitTree.branch 447 (VisitTree.leaf 444 [79, 509]) (VisitTree.leaf 447 [470]))))) (VisitTree.branch 464 (VisitTree.branch 460 (VisitTree.branch 450 (VisitTree.leaf 449 [490]) (VisitTree.leaf 450 [492])) (VisitTree.branch 462 (VisitTree.leaf 460 [489]) (VisitTree.branch 463 (VisitTree.leaf 462 [506]) (VisitTree.leaf 463 [506, 506])))) (VisitTree.branch 466 (VisitTree.branch 465 (VisitTree.leaf 464 [506, 506]) (VisitTree.leaf 465 [507])) (VisitTree.branch 467 (VisitTree.leaf 466 [508, 508]) (VisitTree.branch 468 (VisitTree.leaf 467 [508]) (VisitTree.leaf 468 [509])))))) (VisitTree.branch 647 (VisitTree.branch 628 (VisitTree.branch 608 (VisitTree.branch 471 (VisitTree.leaf 470 [79]) (VisitTree.leaf 471 [509, 509])) (VisitTree.branch 610 (VisitTree.leaf 608 [456]) (VisitTree.branch 623 (VisitTree.leaf 610 [505]) (VisitTree.leaf 623 [495])))) (VisitTree.branch 644 (VisitTree.branch 643 (VisitTree.leaf 628 [500]) (VisitTree.leaf 643 [493])) (VisitTree.branch 645 (VisitTree.leaf 644 [492]) (VisitTree.branch 646 (VisitTree.leaf 645 [491]) (VisitTree.leaf 646 [490]))))) (VisitTree.branch 654 (VisitTree.branch 650 (VisitTree.branch 649 (VisitTree.leaf 647 [489]) (VisitTree.leaf 649 [499])) (VisitTree.branch 651 (VisitTree.leaf 650 [498]) (VisitTree.branch 652 (VisitTree.leaf 651 [497]) (VisitTree.leaf 652 [496])))) (VisitTree.branch 658 (VisitTree.branch 656 (VisitTree.leaf 654 [494]) (VisitTree.branch 657 (VisitTree.leaf 656 [504]) (VisitTree.leaf 657 [503]))) (VisitTree.branch 659 (VisitTree.leaf 658 [502]) (VisitTree.branch 660 (VisitTree.leaf 659 [501]) (VisitTree.leaf 660 [455]))))))))

def fastForwardChunkVisits065 (r : Nat) : List Nat :=
  forwardVisitTree065.lookup r

private theorem covered065 :
    visitsCovered forwardEventChunk065 forwardVisitTree065 = true := by
  decide +kernel

private theorem checked065 :
    visitsChecked forwardEventChunk065 forwardVisitTree065 = true := by
  decide +kernel

theorem eventVisits_forwardChunk065 (r : Nat) :
    eventVisits r forwardEventChunk065 = fastForwardChunkVisits065 r :=
  eventVisits_of_tree _ _ covered065 checked065 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk065

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 66. -/
def forwardVisitTree066 : VisitTree := (VisitTree.branch 413 (VisitTree.branch 295 (VisitTree.branch 267 (VisitTree.branch 254 (VisitTree.branch 245 (VisitTree.leaf 237 [483]) (VisitTree.branch 248 (VisitTree.leaf 245 [497]) (VisitTree.leaf 248 [444]))) (VisitTree.branch 259 (VisitTree.branch 257 (VisitTree.leaf 254 [465]) (VisitTree.leaf 257 [399])) (VisitTree.branch 263 (VisitTree.leaf 259 [461]) (VisitTree.leaf 263 [483])))) (VisitTree.branch 283 (VisitTree.branch 273 (VisitTree.branch 271 (VisitTree.leaf 267 [478]) (VisitTree.leaf 271 [382])) (VisitTree.branch 278 (VisitTree.leaf 273 [401]) (VisitTree.leaf 278 [372]))) (VisitTree.branch 290 (VisitTree.branch 284 (VisitTree.leaf 283 [465]) (VisitTree.leaf 284 [485])) (VisitTree.branch 293 (VisitTree.leaf 290 [501]) (VisitTree.leaf 293 [380]))))) (VisitTree.branch 367 (VisitTree.branch 322 (VisitTree.branch 311 (VisitTree.branch 307 (VisitTree.leaf 295 [491]) (VisitTree.leaf 307 [441])) (VisitTree.branch 314 (VisitTree.leaf 311 [490]) (VisitTree.leaf 314 [461]))) (VisitTree.branch 333 (VisitTree.branch 327 (VisitTree.leaf 322 [349]) (VisitTree.leaf 327 [406])) (VisitTree.branch 360 (VisitTree.leaf 333 [371]) (VisitTree.leaf 360 [331])))) (VisitTree.branch 381 (VisitTree.branch 375 (VisitTree.branch 368 (VisitTree.leaf 367 [441]) (VisitTree.leaf 368 [420])) (VisitTree.branch 377 (VisitTree.leaf 375 [332]) (VisitTree.leaf 377 [408]))) (VisitTree.branch 396 (VisitTree.branch 382 (VisitTree.leaf 381 [332]) (VisitTree.leaf 382 [438])) (VisitTree.branch 398 (VisitTree.leaf 396 [364]) (VisitTree.leaf 398 [449])))))) (VisitTree.branch 538 (VisitTree.branch 469 (VisitTree.branch 435 (VisitTree.branch 423 (VisitTree.branch 416 (VisitTree.leaf 413 [390, 517]) (VisitTree.leaf 416 [426])) (VisitTree.branch 433 (VisitTree.leaf 423 [458]) (VisitTree.leaf 433 [418]))) (VisitTree.branch 451 (VisitTree.branch 445 (VisitTree.leaf 435 [478]) (VisitTree.leaf 445 [447])) (VisitTree.branch 459 (VisitTree.leaf 451 [447]) (VisitTree.leaf 459 [458])))) (VisitTree.branch 519 (VisitTree.branch 486 (VisitTree.branch 482 (VisitTree.leaf 469 [517]) (VisitTree.leaf 482 [380])) (VisitTree.branch 504 (VisitTree.leaf 486 [349]) (VisitTree.leaf 504 [331]))) (VisitTree.branch 524 (VisitTree.branch 520 (VisitTree.leaf 519 [401]) (VisitTree.leaf 520 [364])) (VisitTree.branch 525 (VisitTree.leaf 524 [408]) (VisitTree.leaf 525 [371]))))) (VisitTree.branch 603 (VisitTree.branch 562 (VisitTree.branch 554 (VisitTree.branch 542 (VisitTree.leaf 538 [418]) (VisitTree.leaf 542 [426])) (VisitTree.branch 557 (VisitTree.leaf 554 [420]) (VisitTree.leaf 557 [399]))) (VisitTree.branch 574 (VisitTree.branch 571 (VisitTree.leaf 562 [406]) (VisitTree.leaf 571 [444])) (VisitTree.branch 595 (VisitTree.leaf 574 [382]) (VisitTree.leaf 595 [372])))) (VisitTree.branch 645 (VisitTree.branch 619 (VisitTree.branch 606 (VisitTree.leaf 603 [449]) (VisitTree.leaf 606 [390])) (VisitTree.branch 639 (VisitTree.leaf 619 [438]) (VisitTree.leaf 639 [485]))) (VisitTree.branch 651 (VisitTree.branch 646 (VisitTree.leaf 645 [491]) (VisitTree.leaf 646 [490])) (VisitTree.branch 659 (VisitTree.leaf 651 [497]) (VisitTree.leaf 659 [501])))))))

def fastForwardChunkVisits066 (r : Nat) : List Nat :=
  forwardVisitTree066.lookup r

private theorem covered066 :
    visitsCovered forwardEventChunk066 forwardVisitTree066 = true := by
  decide +kernel

private theorem checked066 :
    visitsChecked forwardEventChunk066 forwardVisitTree066 = true := by
  decide +kernel

theorem eventVisits_forwardChunk066 (r : Nat) :
    eventVisits r forwardEventChunk066 = fastForwardChunkVisits066 r :=
  eventVisits_of_tree _ _ covered066 checked066 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk066

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 67. -/
def forwardVisitTree067 : VisitTree := (VisitTree.branch 352 (VisitTree.branch 288 (VisitTree.branch 244 (VisitTree.branch 233 (VisitTree.branch 226 (VisitTree.leaf 222 [374]) (VisitTree.branch 229 (VisitTree.leaf 226 [475]) (VisitTree.leaf 229 [336]))) (VisitTree.branch 240 (VisitTree.branch 234 (VisitTree.leaf 233 [352]) (VisitTree.leaf 234 [328])) (VisitTree.branch 241 (VisitTree.leaf 240 [510]) (VisitTree.leaf 241 [361])))) (VisitTree.branch 266 (VisitTree.branch 250 (VisitTree.branch 246 (VisitTree.leaf 244 [439]) (VisitTree.leaf 246 [346])) (VisitTree.branch 252 (VisitTree.leaf 250 [505]) (VisitTree.leaf 252 [367]))) (VisitTree.branch 277 (VisitTree.branch 276 (VisitTree.leaf 266 [469]) (VisitTree.leaf 276 [481])) (VisitTree.branch 287 (VisitTree.leaf 277 [475]) (VisitTree.leaf 287 [412]))))) (VisitTree.branch 320 (VisitTree.branch 297 (VisitTree.branch 294 (VisitTree.leaf 288 [499]) (VisitTree.branch 296 (VisitTree.leaf 294 [427]) (VisitTree.leaf 296 [391]))) (VisitTree.branch 316 (VisitTree.branch 305 (VisitTree.leaf 297 [427]) (VisitTree.leaf 305 [351])) (VisitTree.branch 319 (VisitTree.leaf 316 [505]) (VisitTree.leaf 319 [357])))) (VisitTree.branch 340 (VisitTree.branch 332 (VisitTree.branch 328 (VisitTree.leaf 320 [361]) (VisitTree.leaf 328 [432])) (VisitTree.branch 337 (VisitTree.leaf 332 [374]) (VisitTree.leaf 337 [393, 513]))) (VisitTree.branch 344 (VisitTree.branch 343 (VisitTree.leaf 340 [351]) (VisitTree.leaf 343 [411])) (VisitTree.branch 349 (VisitTree.leaf 344 [352]) (VisitTree.leaf 349 [511])))))) (VisitTree.branch 407 (VisitTree.branch 369 (VisitTree.branch 358 (VisitTree.branch 353 (VisitTree.leaf 352 [393]) (VisitTree.branch 357 (VisitTree.leaf 353 [428]) (VisitTree.leaf 357 [341]))) (VisitTree.branch 363 (VisitTree.branch 360 (VisitTree.leaf 358 [340]) (VisitTree.leaf 360 [510])) (VisitTree.branch 365 (VisitTree.leaf 363 [376]) (VisitTree.leaf 365 [432])))) (VisitTree.branch 386 (VisitTree.branch 381 (VisitTree.branch 371 (VisitTree.leaf 369 [392]) (VisitTree.leaf 371 [391])) (VisitTree.branch 385 (VisitTree.leaf 381 [512]) (VisitTree.leaf 385 [428]))) (VisitTree.branch 394 (VisitTree.branch 387 (VisitTree.leaf 386 [411]) (VisitTree.leaf 387 [357])) (VisitTree.branch 400 (VisitTree.leaf 394 [499]) (VisitTree.leaf 400 [335]))))) (VisitTree.branch 452 (VisitTree.branch 430 (VisitTree.branch 411 (VisitTree.branch 409 (VisitTree.leaf 407 [376]) (VisitTree.leaf 409 [340])) (VisitTree.branch 428 (VisitTree.leaf 411 [439]) (VisitTree.leaf 428 [469]))) (VisitTree.branch 444 (VisitTree.branch 443 (VisitTree.leaf 430 [341]) (VisitTree.leaf 443 [367])) (VisitTree.branch 448 (VisitTree.leaf 444 [392, 513]) (VisitTree.leaf 448 [412])))) (VisitTree.branch 475 (VisitTree.branch 473 (VisitTree.branch 472 (VisitTree.leaf 452 [481]) (VisitTree.leaf 472 [328, 510])) (VisitTree.branch 474 (VisitTree.leaf 473 [346, 511]) (VisitTree.leaf 474 [335, 512]))) (VisitTree.branch 487 (VisitTree.branch 486 (VisitTree.leaf 475 [394, 513]) (VisitTree.leaf 486 [511])) (VisitTree.branch 509 (VisitTree.leaf 487 [394]) (VisitTree.leaf 509 [336, 512])))))))

def fastForwardChunkVisits067 (r : Nat) : List Nat :=
  forwardVisitTree067.lookup r

private theorem covered067 :
    visitsCovered forwardEventChunk067 forwardVisitTree067 = true := by
  decide +kernel

private theorem checked067 :
    visitsChecked forwardEventChunk067 forwardVisitTree067 = true := by
  decide +kernel

theorem eventVisits_forwardChunk067 (r : Nat) :
    eventVisits r forwardEventChunk067 = fastForwardChunkVisits067 r :=
  eventVisits_of_tree _ _ covered067 checked067 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk067


