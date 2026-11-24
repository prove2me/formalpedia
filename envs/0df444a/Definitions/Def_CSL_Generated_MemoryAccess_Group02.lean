-- Prove2me | Definitions.Def_CSL_Generated_MemoryAccess_Group02
-- name    : CSL_Generated_MemoryAccess_Group02
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T13:32:07.701241+00:00
-- url     : https://prove2.me/theorems/9e98e994-17c9-4df1-ac5e-1bcce6a2fda7
-- title:
--   Coded sorting library: Generated / MemoryAccess / Group02
-- statement:
--   Module `CodedSorting.Generated.MemoryAccess.Group02` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Generated.MemoryAccess.Group02

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Circuit_MemoryAccess_PhysicalFrameEventChunkData
import Definitions.Def_CSL_Generated_MemoryAccess_Base

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 36. -/
def forwardVisitTree036 : VisitTree := (VisitTree.branch 362 (VisitTree.branch 315 (VisitTree.branch 270 (VisitTree.branch 265 (VisitTree.leaf 224 [288, 288, 288, 288, 288]) (VisitTree.leaf 265 [287, 287, 287, 287])) (VisitTree.branch 286 (VisitTree.leaf 270 [287, 287, 287, 287]) (VisitTree.leaf 286 [287, 287, 287]))) (VisitTree.branch 326 (VisitTree.branch 324 (VisitTree.leaf 315 [287, 287, 287, 287]) (VisitTree.leaf 324 [288, 288, 288, 288, 288, 288, 288, 288])) (VisitTree.branch 335 (VisitTree.leaf 326 [288, 288, 288, 288, 288, 288, 288]) (VisitTree.leaf 335 [289])))) (VisitTree.branch 488 (VisitTree.branch 454 (VisitTree.branch 446 (VisitTree.leaf 362 [288, 288, 288, 288, 288]) (VisitTree.leaf 446 [288, 288, 288, 288, 288])) (VisitTree.branch 487 (VisitTree.leaf 454 [289]) (VisitTree.leaf 487 [289, 289, 289]))) (VisitTree.branch 506 (VisitTree.branch 505 (VisitTree.leaf 488 [287, 287, 287]) (VisitTree.leaf 505 [288, 288, 288, 288, 288, 288])) (VisitTree.branch 510 (VisitTree.leaf 506 [287, 287, 287, 287]) (VisitTree.leaf 510 [289])))))

def fastForwardChunkVisits036 (r : Nat) : List Nat :=
  forwardVisitTree036.lookup r

private theorem covered036 :
    visitsCovered forwardEventChunk036 forwardVisitTree036 = true := by
  decide +kernel

private theorem checked036 :
    visitsChecked forwardEventChunk036 forwardVisitTree036 = true := by
  decide +kernel

theorem eventVisits_forwardChunk036 (r : Nat) :
    eventVisits r forwardEventChunk036 = fastForwardChunkVisits036 r :=
  eventVisits_of_tree _ _ covered036 checked036 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk036

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 37. -/
def forwardVisitTree037 : VisitTree := (VisitTree.branch 370 (VisitTree.branch 337 (VisitTree.branch 239 (VisitTree.leaf 230 [290, 290, 290, 290, 290, 290, 290]) (VisitTree.branch 335 (VisitTree.leaf 239 [289, 289, 289, 289, 289, 289, 289, 289]) (VisitTree.leaf 335 [289, 289, 289, 289, 289]))) (VisitTree.branch 347 (VisitTree.leaf 337 [290, 290, 290, 290, 290]) (VisitTree.branch 364 (VisitTree.leaf 347 [290, 290, 290, 290, 290]) (VisitTree.leaf 364 [289, 289, 289, 289, 289, 289, 289])))) (VisitTree.branch 454 (VisitTree.branch 373 (VisitTree.leaf 370 [290, 290, 290, 290]) (VisitTree.branch 453 (VisitTree.leaf 373 [290, 290, 290, 290, 290]) (VisitTree.leaf 453 [290, 290, 290, 290]))) (VisitTree.branch 487 (VisitTree.leaf 454 [289, 289, 289, 289, 289, 289]) (VisitTree.branch 510 (VisitTree.leaf 487 [289, 289, 289, 289]) (VisitTree.leaf 510 [289, 289, 289, 289])))))

def fastForwardChunkVisits037 (r : Nat) : List Nat :=
  forwardVisitTree037.lookup r

private theorem covered037 :
    visitsCovered forwardEventChunk037 forwardVisitTree037 = true := by
  decide +kernel

private theorem checked037 :
    visitsChecked forwardEventChunk037 forwardVisitTree037 = true := by
  decide +kernel

theorem eventVisits_forwardChunk037 (r : Nat) :
    eventVisits r forwardEventChunk037 = fastForwardChunkVisits037 r :=
  eventVisits_of_tree _ _ covered037 checked037 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk037

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 38. -/
def forwardVisitTree038 : VisitTree := (VisitTree.branch 376 (VisitTree.branch 337 (VisitTree.branch 285 (VisitTree.branch 251 (VisitTree.leaf 230 [290]) (VisitTree.leaf 251 [291, 291, 291, 291, 291, 291, 291, 291])) (VisitTree.branch 323 (VisitTree.leaf 285 [292]) (VisitTree.leaf 323 [292, 292, 292, 292]))) (VisitTree.branch 356 (VisitTree.branch 347 (VisitTree.leaf 337 [290, 290]) (VisitTree.leaf 347 [290, 290])) (VisitTree.branch 370 (VisitTree.leaf 356 [291, 291, 291, 291, 291, 291, 291, 291]) (VisitTree.leaf 370 [290, 290])))) (VisitTree.branch 424 (VisitTree.branch 387 (VisitTree.branch 378 (VisitTree.leaf 376 [291, 291, 291, 291, 291, 291, 291]) (VisitTree.leaf 378 [291, 291, 291, 291, 291, 291, 291])) (VisitTree.branch 406 (VisitTree.leaf 387 [292]) (VisitTree.leaf 406 [292]))) (VisitTree.branch 460 (VisitTree.branch 453 (VisitTree.leaf 424 [292]) (VisitTree.leaf 453 [290, 290, 290])) (VisitTree.branch 498 (VisitTree.leaf 460 [291, 291, 291, 291, 291, 291, 291, 291]) (VisitTree.leaf 498 [291, 291, 291, 291, 291, 291, 291, 291])))))

def fastForwardChunkVisits038 (r : Nat) : List Nat :=
  forwardVisitTree038.lookup r

private theorem covered038 :
    visitsCovered forwardEventChunk038 forwardVisitTree038 = true := by
  decide +kernel

private theorem checked038 :
    visitsChecked forwardEventChunk038 forwardVisitTree038 = true := by
  decide +kernel

theorem eventVisits_forwardChunk038 (r : Nat) :
    eventVisits r forwardEventChunk038 = fastForwardChunkVisits038 r :=
  eventVisits_of_tree _ _ covered038 checked038 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk038

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 39. -/
def forwardVisitTree039 : VisitTree := (VisitTree.branch 387 (VisitTree.branch 323 (VisitTree.branch 285 (VisitTree.leaf 264 [293, 293, 293, 293, 293]) (VisitTree.branch 289 (VisitTree.leaf 285 [292, 292, 292, 292, 292, 292]) (VisitTree.leaf 289 [293, 293, 293, 293, 293, 293]))) (VisitTree.branch 361 (VisitTree.leaf 323 [292, 292, 292, 292]) (VisitTree.branch 366 (VisitTree.leaf 361 [292, 292, 292, 292, 292]) (VisitTree.leaf 366 [293, 293, 293, 293, 293])))) (VisitTree.branch 424 (VisitTree.branch 395 (VisitTree.leaf 387 [292, 292, 292, 292]) (VisitTree.branch 406 (VisitTree.leaf 395 [293, 293, 293, 293, 293, 293]) (VisitTree.leaf 406 [292, 292, 292, 292, 292, 292]))) (VisitTree.branch 445 (VisitTree.leaf 424 [292, 292, 292, 292, 292, 292, 292]) (VisitTree.branch 497 (VisitTree.leaf 445 [293, 293, 293, 293]) (VisitTree.leaf 497 [293, 293, 293, 293, 293, 293])))))

def fastForwardChunkVisits039 (r : Nat) : List Nat :=
  forwardVisitTree039.lookup r

private theorem covered039 :
    visitsCovered forwardEventChunk039 forwardVisitTree039 = true := by
  decide +kernel

private theorem checked039 :
    visitsChecked forwardEventChunk039 forwardVisitTree039 = true := by
  decide +kernel

theorem eventVisits_forwardChunk039 (r : Nat) :
    eventVisits r forwardEventChunk039 = fastForwardChunkVisits039 r :=
  eventVisits_of_tree _ _ covered039 checked039 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk039

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 40. -/
def forwardVisitTree040 : VisitTree := (VisitTree.branch 367 (VisitTree.branch 292 (VisitTree.branch 269 (VisitTree.branch 264 (VisitTree.leaf 255 [294, 294, 294, 294, 294, 294, 294]) (VisitTree.leaf 264 [293])) (VisitTree.branch 282 (VisitTree.leaf 269 [295, 295, 295]) (VisitTree.leaf 282 [294, 294, 294, 294, 294, 294]))) (VisitTree.branch 313 (VisitTree.branch 306 (VisitTree.leaf 292 [295, 295, 295]) (VisitTree.leaf 306 [294, 294, 294, 294, 294, 294])) (VisitTree.branch 336 (VisitTree.leaf 313 [295, 295]) (VisitTree.leaf 336 [294, 294, 294, 294, 294, 294, 294, 294])))) (VisitTree.branch 420 (VisitTree.branch 395 (VisitTree.branch 372 (VisitTree.leaf 367 [294, 294, 294, 294, 294]) (VisitTree.leaf 372 [295, 295, 295, 295])) (VisitTree.branch 409 (VisitTree.leaf 395 [293]) (VisitTree.leaf 409 [294, 294, 294, 294, 294, 294, 294, 294]))) (VisitTree.branch 496 (VisitTree.branch 445 (VisitTree.leaf 420 [295, 295, 295, 295]) (VisitTree.leaf 445 [293])) (VisitTree.branch 497 (VisitTree.leaf 496 [295, 295, 295, 295]) (VisitTree.leaf 497 [293])))))

def fastForwardChunkVisits040 (r : Nat) : List Nat :=
  forwardVisitTree040.lookup r

private theorem covered040 :
    visitsCovered forwardEventChunk040 forwardVisitTree040 = true := by
  decide +kernel

private theorem checked040 :
    visitsChecked forwardEventChunk040 forwardVisitTree040 = true := by
  decide +kernel

theorem eventVisits_forwardChunk040 (r : Nat) :
    eventVisits r forwardEventChunk040 = fastForwardChunkVisits040 r :=
  eventVisits_of_tree _ _ covered040 checked040 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk040

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 41. -/
def forwardVisitTree041 : VisitTree := (VisitTree.branch 372 (VisitTree.branch 303 (VisitTree.branch 279 (VisitTree.leaf 269 [295, 295, 295, 295, 295]) (VisitTree.branch 292 (VisitTree.leaf 279 [296, 296, 296, 296, 296, 296, 296]) (VisitTree.leaf 292 [295, 295, 295, 295, 295]))) (VisitTree.branch 313 (VisitTree.leaf 303 [296, 296, 296, 296, 296, 296]) (VisitTree.branch 348 (VisitTree.leaf 313 [295, 295, 295, 295]) (VisitTree.leaf 348 [296, 296, 296, 296, 296, 296, 296])))) (VisitTree.branch 430 (VisitTree.branch 384 (VisitTree.leaf 372 [295, 295, 295, 295]) (VisitTree.branch 420 (VisitTree.leaf 384 [296, 296, 296, 296, 296, 296, 296]) (VisitTree.leaf 420 [295, 295, 295, 295]))) (VisitTree.branch 496 (VisitTree.leaf 430 [296, 296, 296, 296, 296, 296]) (VisitTree.branch 514 (VisitTree.leaf 496 [295, 295, 295, 295]) (VisitTree.leaf 514 [296, 296, 296, 296, 296])))))

def fastForwardChunkVisits041 (r : Nat) : List Nat :=
  forwardVisitTree041.lookup r

private theorem covered041 :
    visitsCovered forwardEventChunk041 forwardVisitTree041 = true := by
  decide +kernel

private theorem checked041 :
    visitsChecked forwardEventChunk041 forwardVisitTree041 = true := by
  decide +kernel

theorem eventVisits_forwardChunk041 (r : Nat) :
    eventVisits r forwardEventChunk041 = fastForwardChunkVisits041 r :=
  eventVisits_of_tree _ _ covered041 checked041 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk041

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 42. -/
def forwardVisitTree042 : VisitTree := (VisitTree.branch 422 (VisitTree.branch 317 (VisitTree.branch 291 (VisitTree.leaf 267 [297, 297, 297, 297, 297, 297]) (VisitTree.branch 301 (VisitTree.leaf 291 [297, 297, 297, 297, 297]) (VisitTree.leaf 301 [298, 298, 298, 298, 298]))) (VisitTree.branch 321 (VisitTree.leaf 317 [297, 297, 297, 297, 297, 297, 297, 297, 297]) (VisitTree.branch 388 (VisitTree.leaf 321 [298, 298, 298, 298, 298]) (VisitTree.leaf 388 [298, 298, 298, 298])))) (VisitTree.branch 495 (VisitTree.branch 432 (VisitTree.leaf 422 [298, 298, 298, 298]) (VisitTree.branch 438 (VisitTree.leaf 432 [298, 298, 298, 298]) (VisitTree.leaf 438 [297, 297, 297, 297, 297, 297, 297]))) (VisitTree.branch 513 (VisitTree.leaf 495 [297, 297, 297, 297, 297, 297, 297, 297]) (VisitTree.branch 515 (VisitTree.leaf 513 [297, 297, 297, 297, 297]) (VisitTree.leaf 515 [298, 298])))))

def fastForwardChunkVisits042 (r : Nat) : List Nat :=
  forwardVisitTree042.lookup r

private theorem covered042 :
    visitsCovered forwardEventChunk042 forwardVisitTree042 = true := by
  decide +kernel

private theorem checked042 :
    visitsChecked forwardEventChunk042 forwardVisitTree042 = true := by
  decide +kernel

theorem eventVisits_forwardChunk042 (r : Nat) :
    eventVisits r forwardEventChunk042 = fastForwardChunkVisits042 r :=
  eventVisits_of_tree _ _ covered042 checked042 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk042

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 43. -/
def forwardVisitTree043 : VisitTree := (VisitTree.branch 388 (VisitTree.branch 320 (VisitTree.branch 301 (VisitTree.branch 262 (VisitTree.leaf 225 [300]) (VisitTree.leaf 262 [299, 299, 299, 299, 299, 299, 299, 299])) (VisitTree.branch 314 (VisitTree.leaf 301 [298]) (VisitTree.leaf 314 [299, 299, 299, 299, 299, 299]))) (VisitTree.branch 328 (VisitTree.branch 321 (VisitTree.leaf 320 [300, 300, 300, 300]) (VisitTree.leaf 321 [298, 298, 298])) (VisitTree.branch 330 (VisitTree.leaf 328 [300]) (VisitTree.leaf 330 [300])))) (VisitTree.branch 440 (VisitTree.branch 422 (VisitTree.branch 402 (VisitTree.leaf 388 [298, 298, 298]) (VisitTree.leaf 402 [299, 299, 299, 299, 299, 299, 299, 299])) (VisitTree.branch 432 (VisitTree.leaf 422 [298, 298, 298]) (VisitTree.leaf 432 [298]))) (VisitTree.branch 494 (VisitTree.branch 458 (VisitTree.leaf 440 [299, 299, 299, 299, 299, 299, 299]) (VisitTree.leaf 458 [300])) (VisitTree.branch 512 (VisitTree.leaf 494 [299, 299, 299, 299, 299, 299, 299, 299]) (VisitTree.branch 515 (VisitTree.leaf 512 [299, 299, 299, 299, 299]) (VisitTree.leaf 515 [298, 298, 298]))))))

def fastForwardChunkVisits043 (r : Nat) : List Nat :=
  forwardVisitTree043.lookup r

private theorem covered043 :
    visitsCovered forwardEventChunk043 forwardVisitTree043 = true := by
  decide +kernel

private theorem checked043 :
    visitsChecked forwardEventChunk043 forwardVisitTree043 = true := by
  decide +kernel

theorem eventVisits_forwardChunk043 (r : Nat) :
    eventVisits r forwardEventChunk043 = fastForwardChunkVisits043 r :=
  eventVisits_of_tree _ _ covered043 checked043 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk043

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 44. -/
def forwardVisitTree044 : VisitTree := (VisitTree.branch 448 (VisitTree.branch 330 (VisitTree.branch 320 (VisitTree.leaf 225 [300, 300, 300, 300, 300, 300]) (VisitTree.branch 328 (VisitTree.leaf 320 [300, 300, 300, 300]) (VisitTree.leaf 328 [300, 300, 300, 300, 300, 300, 300]))) (VisitTree.branch 350 (VisitTree.leaf 330 [300, 300, 300, 300, 300, 300]) (VisitTree.branch 363 (VisitTree.leaf 350 [301, 301, 301, 301]) (VisitTree.leaf 363 [301, 301, 301, 301, 301])))) (VisitTree.branch 493 (VisitTree.branch 450 (VisitTree.leaf 448 [301, 301, 301, 301, 301]) (VisitTree.branch 458 (VisitTree.leaf 450 [301, 301, 301, 301]) (VisitTree.leaf 458 [300, 300, 300, 300, 300, 300, 300]))) (VisitTree.branch 511 (VisitTree.leaf 493 [301, 301, 301, 301]) (VisitTree.branch 516 (VisitTree.leaf 511 [300, 300, 300, 300, 300, 300, 300, 300]) (VisitTree.leaf 516 [301, 301, 301, 301])))))

def fastForwardChunkVisits044 (r : Nat) : List Nat :=
  forwardVisitTree044.lookup r

private theorem covered044 :
    visitsCovered forwardEventChunk044 forwardVisitTree044 = true := by
  decide +kernel

private theorem checked044 :
    visitsChecked forwardEventChunk044 forwardVisitTree044 = true := by
  decide +kernel

theorem eventVisits_forwardChunk044 (r : Nat) :
    eventVisits r forwardEventChunk044 = fastForwardChunkVisits044 r :=
  eventVisits_of_tree _ _ covered044 checked044 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk044

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 45. -/
def forwardVisitTree045 : VisitTree := (VisitTree.branch 548 (VisitTree.branch 493 (VisitTree.branch 448 (VisitTree.branch 363 (VisitTree.leaf 350 [301, 301, 301]) (VisitTree.leaf 363 [301, 301])) (VisitTree.branch 450 (VisitTree.leaf 448 [301, 301, 301]) (VisitTree.leaf 450 [301, 301, 301, 301]))) (VisitTree.branch 521 (VisitTree.branch 516 (VisitTree.leaf 493 [301, 301, 301, 301]) (VisitTree.leaf 516 [301, 301, 301, 301])) (VisitTree.branch 522 (VisitTree.leaf 521 [303, 303, 303, 303]) (VisitTree.branch 539 (VisitTree.leaf 522 [302, 302, 302, 302, 302, 302, 302]) (VisitTree.leaf 539 [303, 303]))))) (VisitTree.branch 587 (VisitTree.branch 557 (VisitTree.branch 553 (VisitTree.leaf 548 [302, 302, 302, 302, 302, 302]) (VisitTree.leaf 553 [302, 302])) (VisitTree.branch 575 (VisitTree.leaf 557 [303]) (VisitTree.leaf 575 [303, 303]))) (VisitTree.branch 607 (VisitTree.branch 604 (VisitTree.leaf 587 [302, 302, 302, 302, 302, 302, 302]) (VisitTree.leaf 604 [302, 302, 302, 302, 302])) (VisitTree.branch 630 (VisitTree.leaf 607 [303, 303]) (VisitTree.branch 652 (VisitTree.leaf 630 [303]) (VisitTree.leaf 652 [302, 302, 302, 302, 302]))))))

def fastForwardChunkVisits045 (r : Nat) : List Nat :=
  forwardVisitTree045.lookup r

private theorem covered045 :
    visitsCovered forwardEventChunk045 forwardVisitTree045 = true := by
  decide +kernel

private theorem checked045 :
    visitsChecked forwardEventChunk045 forwardVisitTree045 = true := by
  decide +kernel

theorem eventVisits_forwardChunk045 (r : Nat) :
    eventVisits r forwardEventChunk045 = fastForwardChunkVisits045 r :=
  eventVisits_of_tree _ _ covered045 checked045 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk045

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 46. -/
def forwardVisitTree046 : VisitTree := (VisitTree.branch 591 (VisitTree.branch 556 (VisitTree.branch 521 (VisitTree.leaf 520 [304, 304, 304, 304, 304, 304]) (VisitTree.branch 539 (VisitTree.leaf 521 [303, 303, 303, 303]) (VisitTree.leaf 539 [303, 303, 303, 303, 303]))) (VisitTree.branch 557 (VisitTree.leaf 556 [304, 304, 304, 304, 304, 304]) (VisitTree.branch 575 (VisitTree.leaf 557 [303, 303, 303, 303, 303]) (VisitTree.leaf 575 [303, 303, 303, 303])))) (VisitTree.branch 630 (VisitTree.branch 607 (VisitTree.leaf 591 [304, 304, 304, 304, 304]) (VisitTree.branch 618 (VisitTree.leaf 607 [303, 303, 303, 303, 303]) (VisitTree.leaf 618 [304, 304, 304, 304]))) (VisitTree.branch 637 (VisitTree.leaf 630 [303, 303, 303, 303, 303, 303, 303]) (VisitTree.branch 646 (VisitTree.leaf 637 [304, 304, 304, 304, 304, 304]) (VisitTree.leaf 646 [304, 304, 304, 304, 304, 304, 304])))))

def fastForwardChunkVisits046 (r : Nat) : List Nat :=
  forwardVisitTree046.lookup r

private theorem covered046 :
    visitsCovered forwardEventChunk046 forwardVisitTree046 = true := by
  decide +kernel

private theorem checked046 :
    visitsChecked forwardEventChunk046 forwardVisitTree046 = true := by
  decide +kernel

theorem eventVisits_forwardChunk046 (r : Nat) :
    eventVisits r forwardEventChunk046 = fastForwardChunkVisits046 r :=
  eventVisits_of_tree _ _ covered046 checked046 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk046

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 47. -/
def forwardVisitTree047 : VisitTree := (VisitTree.branch 591 (VisitTree.branch 554 (VisitTree.branch 520 (VisitTree.branch 519 (VisitTree.leaf 518 [306, 306, 306]) (VisitTree.leaf 519 [305, 305, 305, 305, 305, 305, 305, 305])) (VisitTree.branch 536 (VisitTree.leaf 520 [304, 304]) (VisitTree.leaf 536 [306, 306, 306, 306]))) (VisitTree.branch 556 (VisitTree.branch 555 (VisitTree.leaf 554 [306, 306]) (VisitTree.leaf 555 [305, 305, 305, 305, 305, 305, 305, 305])) (VisitTree.branch 572 (VisitTree.leaf 556 [304, 304]) (VisitTree.leaf 572 [306])))) (VisitTree.branch 618 (VisitTree.branch 612 (VisitTree.branch 592 (VisitTree.leaf 591 [304, 304]) (VisitTree.leaf 592 [305, 305, 305, 305, 305, 305])) (VisitTree.branch 613 (VisitTree.leaf 612 [306, 306]) (VisitTree.leaf 613 [305, 305, 305, 305, 305, 305, 305]))) (VisitTree.branch 642 (VisitTree.branch 625 (VisitTree.leaf 618 [304, 304]) (VisitTree.leaf 625 [306, 306])) (VisitTree.branch 645 (VisitTree.leaf 642 [305, 305, 305, 305, 305, 305]) (VisitTree.leaf 645 [305, 305, 305, 305, 305, 305, 305])))))

def fastForwardChunkVisits047 (r : Nat) : List Nat :=
  forwardVisitTree047.lookup r

private theorem covered047 :
    visitsCovered forwardEventChunk047 forwardVisitTree047 = true := by
  decide +kernel

private theorem checked047 :
    visitsChecked forwardEventChunk047 forwardVisitTree047 = true := by
  decide +kernel

theorem eventVisits_forwardChunk047 (r : Nat) :
    eventVisits r forwardEventChunk047 = fastForwardChunkVisits047 r :=
  eventVisits_of_tree _ _ covered047 checked047 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk047

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 48. -/
def forwardVisitTree048 : VisitTree := (VisitTree.branch 572 (VisitTree.branch 551 (VisitTree.branch 518 (VisitTree.leaf 517 [307, 307, 307, 307, 307, 307]) (VisitTree.branch 536 (VisitTree.leaf 518 [306, 306, 306, 306]) (VisitTree.leaf 536 [306, 306, 306, 306]))) (VisitTree.branch 554 (VisitTree.leaf 551 [307, 307, 307]) (VisitTree.branch 558 (VisitTree.leaf 554 [306, 306, 306, 306, 306, 306, 306]) (VisitTree.leaf 558 [307, 307, 307, 307])))) (VisitTree.branch 612 (VisitTree.branch 584 (VisitTree.leaf 572 [306, 306, 306, 306, 306, 306, 306]) (VisitTree.branch 603 (VisitTree.leaf 584 [307, 307, 307, 307, 307, 307, 307]) (VisitTree.leaf 603 [307, 307, 307, 307, 307]))) (VisitTree.branch 625 (VisitTree.leaf 612 [306, 306, 306, 306, 306]) (VisitTree.branch 651 (VisitTree.leaf 625 [306, 306, 306, 306, 306, 306, 306]) (VisitTree.leaf 651 [307, 307, 307, 307, 307])))))

def fastForwardChunkVisits048 (r : Nat) : List Nat :=
  forwardVisitTree048.lookup r

private theorem covered048 :
    visitsCovered forwardEventChunk048 forwardVisitTree048 = true := by
  decide +kernel

private theorem checked048 :
    visitsChecked forwardEventChunk048 forwardVisitTree048 = true := by
  decide +kernel

theorem eventVisits_forwardChunk048 (r : Nat) :
    eventVisits r forwardEventChunk048 = fastForwardChunkVisits048 r :=
  eventVisits_of_tree _ _ covered048 checked048 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk048

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 49. -/
def forwardVisitTree049 : VisitTree := (VisitTree.branch 563 (VisitTree.branch 550 (VisitTree.branch 527 (VisitTree.leaf 517 [307, 307]) (VisitTree.branch 528 (VisitTree.leaf 527 [309, 309, 309, 309, 309]) (VisitTree.leaf 528 [308, 308, 308, 308, 308, 308, 308]))) (VisitTree.branch 558 (VisitTree.branch 551 (VisitTree.leaf 550 [308, 308, 308, 308, 308, 308]) (VisitTree.leaf 551 [307])) (VisitTree.branch 559 (VisitTree.leaf 558 [307]) (VisitTree.leaf 559 [308, 308, 308, 308, 308])))) (VisitTree.branch 622 (VisitTree.branch 600 (VisitTree.branch 585 (VisitTree.leaf 563 [309, 309, 309, 309, 309]) (VisitTree.leaf 585 [308, 308])) (VisitTree.branch 610 (VisitTree.leaf 600 [309, 309, 309, 309, 309]) (VisitTree.leaf 610 [309, 309, 309, 309]))) (VisitTree.branch 634 (VisitTree.branch 627 (VisitTree.leaf 622 [308, 308, 308, 308, 308]) (VisitTree.leaf 627 [309, 309, 309, 309, 309])) (VisitTree.branch 655 (VisitTree.leaf 634 [308, 308, 308, 308, 308]) (VisitTree.leaf 655 [309, 309, 309, 309, 309, 309])))))

def fastForwardChunkVisits049 (r : Nat) : List Nat :=
  forwardVisitTree049.lookup r

private theorem covered049 :
    visitsCovered forwardEventChunk049 forwardVisitTree049 = true := by
  decide +kernel

private theorem checked049 :
    visitsChecked forwardEventChunk049 forwardVisitTree049 = true := by
  decide +kernel

theorem eventVisits_forwardChunk049 (r : Nat) :
    eventVisits r forwardEventChunk049 = fastForwardChunkVisits049 r :=
  eventVisits_of_tree _ _ covered049 checked049 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk049

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 50. -/
def forwardVisitTree050 : VisitTree := (VisitTree.branch 580 (VisitTree.branch 543 (VisitTree.branch 526 (VisitTree.leaf 525 [311, 311, 311, 311]) (VisitTree.branch 527 (VisitTree.leaf 526 [310, 310, 310, 310, 310, 310, 310]) (VisitTree.leaf 527 [309, 309]))) (VisitTree.branch 562 (VisitTree.branch 544 (VisitTree.leaf 543 [310, 310, 310, 310, 310, 310, 310, 310]) (VisitTree.leaf 544 [311, 311, 311, 311])) (VisitTree.branch 579 (VisitTree.leaf 562 [310, 310, 310, 310, 310, 310]) (VisitTree.leaf 579 [310, 310, 310, 310, 310, 310])))) (VisitTree.branch 610 (VisitTree.branch 594 (VisitTree.branch 589 (VisitTree.leaf 580 [311, 311]) (VisitTree.leaf 589 [310, 310, 310, 310, 310, 310, 310])) (VisitTree.branch 600 (VisitTree.leaf 594 [311, 311]) (VisitTree.leaf 600 [309, 309]))) (VisitTree.branch 643 (VisitTree.branch 627 (VisitTree.leaf 610 [309, 309]) (VisitTree.leaf 627 [309, 309])) (VisitTree.branch 648 (VisitTree.leaf 643 [311, 311]) (VisitTree.leaf 648 [310, 310, 310, 310, 310, 310, 310, 310])))))

def fastForwardChunkVisits050 (r : Nat) : List Nat :=
  forwardVisitTree050.lookup r

private theorem covered050 :
    visitsCovered forwardEventChunk050 forwardVisitTree050 = true := by
  decide +kernel

private theorem checked050 :
    visitsChecked forwardEventChunk050 forwardVisitTree050 = true := by
  decide +kernel

theorem eventVisits_forwardChunk050 (r : Nat) :
    eventVisits r forwardEventChunk050 = fastForwardChunkVisits050 r :=
  eventVisits_of_tree _ _ covered050 checked050 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk050

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 51. -/
def forwardVisitTree051 : VisitTree := (VisitTree.branch 594 (VisitTree.branch 560 (VisitTree.branch 525 (VisitTree.leaf 524 [312, 312, 312, 312, 312, 312, 312]) (VisitTree.branch 544 (VisitTree.leaf 525 [311, 311, 311, 311]) (VisitTree.leaf 544 [311]))) (VisitTree.branch 561 (VisitTree.leaf 560 [312, 312, 312]) (VisitTree.branch 580 (VisitTree.leaf 561 [311, 311, 311, 311, 311]) (VisitTree.leaf 580 [311, 311, 311, 311, 311, 311])))) (VisitTree.branch 628 (VisitTree.branch 595 (VisitTree.leaf 594 [311, 311, 311, 311, 311, 311]) (VisitTree.branch 609 (VisitTree.leaf 595 [312, 312, 312, 312, 312, 312, 312]) (VisitTree.leaf 609 [312, 312, 312, 312, 312]))) (VisitTree.branch 643 (VisitTree.leaf 628 [312, 312, 312, 312, 312, 312, 312]) (VisitTree.branch 660 (VisitTree.leaf 643 [311, 311, 311, 311, 311, 311]) (VisitTree.leaf 660 [312, 312, 312, 312, 312, 312, 312])))))

def fastForwardChunkVisits051 (r : Nat) : List Nat :=
  forwardVisitTree051.lookup r

private theorem covered051 :
    visitsCovered forwardEventChunk051 forwardVisitTree051 = true := by
  decide +kernel

private theorem checked051 :
    visitsChecked forwardEventChunk051 forwardVisitTree051 = true := by
  decide +kernel

theorem eventVisits_forwardChunk051 (r : Nat) :
    eventVisits r forwardEventChunk051 = fastForwardChunkVisits051 r :=
  eventVisits_of_tree _ _ covered051 checked051 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk051


