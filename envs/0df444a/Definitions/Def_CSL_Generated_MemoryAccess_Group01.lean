-- Prove2me | Definitions.Def_CSL_Generated_MemoryAccess_Group01
-- name    : CSL_Generated_MemoryAccess_Group01
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T13:29:24.957797+00:00
-- url     : https://prove2.me/theorems/94476a62-cb0c-4b97-8323-7eda116d2cae
-- title:
--   Coded sorting library: Generated / MemoryAccess / Group01
-- statement:
--   Module `CodedSorting.Generated.MemoryAccess.Group01` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Generated.MemoryAccess.Group01

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Circuit_MemoryAccess_PhysicalFrameEventChunkData
import Definitions.Def_CSL_Generated_MemoryAccess_Base

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 20. -/
def forwardVisitTree020 : VisitTree := (VisitTree.branch 418 (VisitTree.branch 239 (VisitTree.branch 90 (VisitTree.branch 18 (VisitTree.branch 14 (VisitTree.leaf 8 [249]) (VisitTree.branch 16 (VisitTree.leaf 14 [236]) (VisitTree.leaf 16 [243]))) (VisitTree.branch 20 (VisitTree.leaf 18 [242]) (VisitTree.branch 88 (VisitTree.leaf 20 [240]) (VisitTree.leaf 88 [247])))) (VisitTree.branch 109 (VisitTree.branch 93 (VisitTree.leaf 90 [239]) (VisitTree.branch 95 (VisitTree.leaf 93 [246]) (VisitTree.leaf 95 [241]))) (VisitTree.branch 110 (VisitTree.leaf 109 [235]) (VisitTree.branch 238 (VisitTree.leaf 110 [250]) (VisitTree.leaf 238 [248, 248]))))) (VisitTree.branch 262 (VisitTree.branch 255 (VisitTree.branch 248 (VisitTree.leaf 239 [250, 250]) (VisitTree.branch 254 (VisitTree.leaf 248 [248]) (VisitTree.leaf 254 [237]))) (VisitTree.branch 258 (VisitTree.leaf 255 [238, 238]) (VisitTree.branch 259 (VisitTree.leaf 258 [242, 242]) (VisitTree.leaf 259 [244])))) (VisitTree.branch 267 (VisitTree.branch 263 (VisitTree.leaf 262 [245, 245]) (VisitTree.branch 266 (VisitTree.leaf 263 [246, 246]) (VisitTree.leaf 266 [236, 236]))) (VisitTree.branch 414 (VisitTree.leaf 267 [239, 239]) (VisitTree.branch 415 (VisitTree.leaf 414 [243, 243]) (VisitTree.leaf 415 [245])))))) (VisitTree.branch 634 (VisitTree.branch 447 (VisitTree.branch 425 (VisitTree.branch 419 (VisitTree.leaf 418 [237, 237]) (VisitTree.branch 424 (VisitTree.leaf 419 [241, 241]) (VisitTree.leaf 424 [244, 244]))) (VisitTree.branch 428 (VisitTree.leaf 425 [247, 247]) (VisitTree.branch 429 (VisitTree.leaf 428 [238]) (VisitTree.leaf 429 [240, 240])))) (VisitTree.branch 631 (VisitTree.branch 450 (VisitTree.leaf 447 [235, 235]) (VisitTree.branch 630 (VisitTree.leaf 450 [249, 249]) (VisitTree.leaf 630 [235]))) (VisitTree.branch 632 (VisitTree.leaf 631 [236]) (VisitTree.branch 633 (VisitTree.leaf 632 [237]) (VisitTree.leaf 633 [238]))))) (VisitTree.branch 640 (VisitTree.branch 637 (VisitTree.branch 635 (VisitTree.leaf 634 [239]) (VisitTree.branch 636 (VisitTree.leaf 635 [240]) (VisitTree.leaf 636 [241]))) (VisitTree.branch 638 (VisitTree.leaf 637 [242]) (VisitTree.branch 639 (VisitTree.leaf 638 [243]) (VisitTree.leaf 639 [244])))) (VisitTree.branch 643 (VisitTree.branch 641 (VisitTree.leaf 640 [245]) (VisitTree.branch 642 (VisitTree.leaf 641 [246]) (VisitTree.leaf 642 [247]))) (VisitTree.branch 644 (VisitTree.leaf 643 [248]) (VisitTree.branch 645 (VisitTree.leaf 644 [249]) (VisitTree.leaf 645 [250])))))))

def fastForwardChunkVisits020 (r : Nat) : List Nat :=
  forwardVisitTree020.lookup r

private theorem covered020 :
    visitsCovered forwardEventChunk020 forwardVisitTree020 = true := by
  decide +kernel

private theorem checked020 :
    visitsChecked forwardEventChunk020 forwardVisitTree020 = true := by
  decide +kernel

theorem eventVisits_forwardChunk020 (r : Nat) :
    eventVisits r forwardEventChunk020 = fastForwardChunkVisits020 r :=
  eventVisits_of_tree _ _ covered020 checked020 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk020

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 21. -/
def forwardVisitTree021 : VisitTree := (VisitTree.branch 392 (VisitTree.branch 244 (VisitTree.branch 78 (VisitTree.branch 40 (VisitTree.branch 31 (VisitTree.leaf 12 [252]) (VisitTree.branch 37 (VisitTree.leaf 31 [256]) (VisitTree.leaf 37 [254]))) (VisitTree.branch 45 (VisitTree.leaf 40 [260]) (VisitTree.branch 73 (VisitTree.leaf 45 [263]) (VisitTree.leaf 73 [265])))) (VisitTree.branch 105 (VisitTree.branch 81 (VisitTree.leaf 78 [264]) (VisitTree.branch 86 (VisitTree.leaf 81 [257]) (VisitTree.leaf 86 [259]))) (VisitTree.branch 236 (VisitTree.leaf 105 [251]) (VisitTree.branch 243 (VisitTree.leaf 236 [266]) (VisitTree.leaf 243 [266, 266]))))) (VisitTree.branch 306 (VisitTree.branch 289 (VisitTree.branch 249 (VisitTree.leaf 244 [266]) (VisitTree.branch 288 (VisitTree.leaf 249 [251, 251]) (VisitTree.leaf 288 [254, 254]))) (VisitTree.branch 300 (VisitTree.leaf 289 [255, 255]) (VisitTree.branch 301 (VisitTree.leaf 300 [257, 257]) (VisitTree.leaf 301 [258, 258])))) (VisitTree.branch 317 (VisitTree.branch 307 (VisitTree.leaf 306 [261, 261]) (VisitTree.branch 316 (VisitTree.leaf 307 [262]) (VisitTree.leaf 316 [260, 260]))) (VisitTree.branch 382 (VisitTree.leaf 317 [264, 264]) (VisitTree.branch 383 (VisitTree.leaf 382 [261]) (VisitTree.leaf 383 [263, 263])))))) (VisitTree.branch 649 (VisitTree.branch 451 (VisitTree.branch 399 (VisitTree.branch 393 (VisitTree.leaf 392 [262, 262]) (VisitTree.branch 398 (VisitTree.leaf 393 [265, 265]) (VisitTree.leaf 398 [255]))) (VisitTree.branch 410 (VisitTree.leaf 399 [259, 259]) (VisitTree.branch 411 (VisitTree.leaf 410 [256, 256]) (VisitTree.leaf 411 [258])))) (VisitTree.branch 646 (VisitTree.branch 460 (VisitTree.leaf 451 [253]) (VisitTree.branch 461 (VisitTree.leaf 460 [252, 252]) (VisitTree.leaf 461 [253, 253]))) (VisitTree.branch 647 (VisitTree.leaf 646 [251]) (VisitTree.branch 648 (VisitTree.leaf 647 [252]) (VisitTree.leaf 648 [253]))))) (VisitTree.branch 655 (VisitTree.branch 652 (VisitTree.branch 650 (VisitTree.leaf 649 [254]) (VisitTree.branch 651 (VisitTree.leaf 650 [255]) (VisitTree.leaf 651 [256]))) (VisitTree.branch 653 (VisitTree.leaf 652 [257]) (VisitTree.branch 654 (VisitTree.leaf 653 [258]) (VisitTree.leaf 654 [259])))) (VisitTree.branch 658 (VisitTree.branch 656 (VisitTree.leaf 655 [260]) (VisitTree.branch 657 (VisitTree.leaf 656 [261]) (VisitTree.leaf 657 [262]))) (VisitTree.branch 659 (VisitTree.leaf 658 [263]) (VisitTree.branch 660 (VisitTree.leaf 659 [264]) (VisitTree.leaf 660 [265])))))))

def fastForwardChunkVisits021 (r : Nat) : List Nat :=
  forwardVisitTree021.lookup r

private theorem covered021 :
    visitsCovered forwardEventChunk021 forwardVisitTree021 = true := by
  decide +kernel

private theorem checked021 :
    visitsChecked forwardEventChunk021 forwardVisitTree021 = true := by
  decide +kernel

theorem eventVisits_forwardChunk021 (r : Nat) :
    eventVisits r forwardEventChunk021 = fastForwardChunkVisits021 r :=
  eventVisits_of_tree _ _ covered021 checked021 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk021

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 22. -/
def forwardVisitTree022 : VisitTree := (VisitTree.branch 247 (VisitTree.branch 238 (VisitTree.branch 226 (VisitTree.leaf 222 [267, 267]) (VisitTree.branch 236 (VisitTree.leaf 226 [266, 266, 266, 266, 266, 266, 266, 266]) (VisitTree.leaf 236 [266, 266, 266, 266, 266, 266, 266]))) (VisitTree.branch 243 (VisitTree.leaf 238 [266, 266, 266, 266, 266, 266, 266, 266]) (VisitTree.branch 244 (VisitTree.leaf 243 [266, 266, 266, 266, 266, 266]) (VisitTree.leaf 244 [266, 266, 266, 266, 266, 266, 266])))) (VisitTree.branch 369 (VisitTree.branch 351 (VisitTree.leaf 247 [266, 266, 266, 266, 266, 266, 266, 266]) (VisitTree.branch 353 (VisitTree.leaf 351 [267, 267, 267, 267, 267]) (VisitTree.leaf 353 [267, 267, 267]))) (VisitTree.branch 379 (VisitTree.leaf 369 [267, 267]) (VisitTree.branch 486 (VisitTree.leaf 379 [267, 267, 267, 267]) (VisitTree.leaf 486 [267, 267, 267, 267])))))

def fastForwardChunkVisits022 (r : Nat) : List Nat :=
  forwardVisitTree022.lookup r

private theorem covered022 :
    visitsCovered forwardEventChunk022 forwardVisitTree022 = true := by
  decide +kernel

private theorem checked022 :
    visitsChecked forwardEventChunk022 forwardVisitTree022 = true := by
  decide +kernel

theorem eventVisits_forwardChunk022 (r : Nat) :
    eventVisits r forwardEventChunk022 = fastForwardChunkVisits022 r :=
  eventVisits_of_tree _ _ covered022 checked022 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk022

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 23. -/
def forwardVisitTree023 : VisitTree := (VisitTree.branch 280 (VisitTree.branch 258 (VisitTree.branch 223 (VisitTree.leaf 222 [267, 267, 267, 267]) (VisitTree.branch 235 (VisitTree.leaf 223 [268, 268, 268, 268, 268, 268]) (VisitTree.leaf 235 [268, 268, 268, 268, 268, 268, 268]))) (VisitTree.branch 260 (VisitTree.leaf 258 [268, 268, 268, 268, 268, 268, 268, 268, 268, 268]) (VisitTree.branch 274 (VisitTree.leaf 260 [268, 268, 268, 268, 268, 268]) (VisitTree.leaf 274 [268, 268, 268, 268, 268, 268, 268, 268])))) (VisitTree.branch 369 (VisitTree.branch 351 (VisitTree.leaf 280 [268, 268, 268, 268, 268]) (VisitTree.branch 353 (VisitTree.leaf 351 [267, 267, 267]) (VisitTree.leaf 353 [267, 267, 267]))) (VisitTree.branch 379 (VisitTree.leaf 369 [267, 267, 267, 267]) (VisitTree.branch 486 (VisitTree.leaf 379 [267, 267, 267, 267]) (VisitTree.leaf 486 [267, 267, 267, 267])))))

def fastForwardChunkVisits023 (r : Nat) : List Nat :=
  forwardVisitTree023.lookup r

private theorem covered023 :
    visitsCovered forwardEventChunk023 forwardVisitTree023 = true := by
  decide +kernel

private theorem checked023 :
    visitsChecked forwardEventChunk023 forwardVisitTree023 = true := by
  decide +kernel

theorem eventVisits_forwardChunk023 (r : Nat) :
    eventVisits r forwardEventChunk023 = fastForwardChunkVisits023 r :=
  eventVisits_of_tree _ _ covered023 checked023 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk023

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 24. -/
def forwardVisitTree024 : VisitTree := (VisitTree.branch 272 (VisitTree.branch 253 (VisitTree.branch 235 (VisitTree.branch 234 (VisitTree.leaf 223 [268, 268]) (VisitTree.leaf 234 [270, 270, 270, 270])) (VisitTree.branch 252 (VisitTree.leaf 235 [268]) (VisitTree.leaf 252 [270]))) (VisitTree.branch 266 (VisitTree.branch 260 (VisitTree.leaf 253 [269, 269, 269, 269, 269]) (VisitTree.leaf 260 [268, 268])) (VisitTree.branch 268 (VisitTree.leaf 266 [270, 270]) (VisitTree.leaf 268 [270, 270])))) (VisitTree.branch 397 (VisitTree.branch 280 (VisitTree.branch 276 (VisitTree.leaf 272 [270, 270, 270, 270, 270]) (VisitTree.leaf 276 [270, 270])) (VisitTree.branch 389 (VisitTree.leaf 280 [268, 268, 268]) (VisitTree.leaf 389 [269, 269, 269, 269, 269, 269]))) (VisitTree.branch 403 (VisitTree.branch 399 (VisitTree.leaf 397 [269, 269, 269, 269, 269, 269]) (VisitTree.leaf 399 [269, 269, 269, 269, 269, 269, 269])) (VisitTree.branch 485 (VisitTree.leaf 403 [269, 269, 269, 269, 269, 269, 269, 269]) (VisitTree.leaf 485 [269, 269, 269, 269, 269, 269, 269, 269])))))

def fastForwardChunkVisits024 (r : Nat) : List Nat :=
  forwardVisitTree024.lookup r

private theorem covered024 :
    visitsCovered forwardEventChunk024 forwardVisitTree024 = true := by
  decide +kernel

private theorem checked024 :
    visitsChecked forwardEventChunk024 forwardVisitTree024 = true := by
  decide +kernel

theorem eventVisits_forwardChunk024 (r : Nat) :
    eventVisits r forwardEventChunk024 = fastForwardChunkVisits024 r :=
  eventVisits_of_tree _ _ covered024 checked024 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk024

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 25. -/
def forwardVisitTree025 : VisitTree := (VisitTree.branch 276 (VisitTree.branch 266 (VisitTree.branch 246 (VisitTree.leaf 234 [270, 270, 270, 270]) (VisitTree.branch 252 (VisitTree.leaf 246 [271, 271, 271, 271, 271, 271]) (VisitTree.leaf 252 [270, 270, 270, 270]))) (VisitTree.branch 268 (VisitTree.leaf 266 [270, 270, 270, 270]) (VisitTree.branch 272 (VisitTree.leaf 268 [270, 270, 270, 270]) (VisitTree.leaf 272 [270, 270])))) (VisitTree.branch 401 (VisitTree.branch 391 (VisitTree.leaf 276 [270, 270, 270, 270]) (VisitTree.branch 393 (VisitTree.leaf 391 [271, 271, 271, 271, 271, 271]) (VisitTree.leaf 393 [271, 271, 271, 271, 271, 271, 271, 271, 271, 271]))) (VisitTree.branch 405 (VisitTree.leaf 401 [271, 271, 271, 271, 271]) (VisitTree.branch 484 (VisitTree.leaf 405 [271, 271, 271, 271, 271, 271, 271, 271]) (VisitTree.leaf 484 [271, 271, 271, 271, 271, 271, 271])))))

def fastForwardChunkVisits025 (r : Nat) : List Nat :=
  forwardVisitTree025.lookup r

private theorem covered025 :
    visitsCovered forwardEventChunk025 forwardVisitTree025 = true := by
  decide +kernel

private theorem checked025 :
    visitsChecked forwardEventChunk025 forwardVisitTree025 = true := by
  decide +kernel

theorem eventVisits_forwardChunk025 (r : Nat) :
    eventVisits r forwardEventChunk025 = fastForwardChunkVisits025 r :=
  eventVisits_of_tree _ _ covered025 checked025 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk025

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 26. -/
def forwardVisitTree026 : VisitTree := (VisitTree.branch 419 (VisitTree.branch 302 (VisitTree.branch 294 (VisitTree.branch 246 (VisitTree.leaf 242 [272, 272, 272, 272, 272, 272, 272, 272]) (VisitTree.leaf 246 [271, 271])) (VisitTree.branch 296 (VisitTree.leaf 294 [272, 272, 272, 272, 272, 272, 272]) (VisitTree.leaf 296 [272, 272, 272, 272, 272, 272, 272, 272]))) (VisitTree.branch 391 (VisitTree.branch 316 (VisitTree.leaf 302 [272, 272, 272, 272, 272, 272, 272]) (VisitTree.leaf 316 [272, 272, 272, 272, 272, 272, 272, 272])) (VisitTree.branch 401 (VisitTree.leaf 391 [271, 271]) (VisitTree.leaf 401 [271, 271, 271])))) (VisitTree.branch 483 (VisitTree.branch 427 (VisitTree.branch 421 (VisitTree.leaf 419 [273]) (VisitTree.leaf 421 [273, 273])) (VisitTree.branch 439 (VisitTree.leaf 427 [273]) (VisitTree.leaf 439 [273]))) (VisitTree.branch 501 (VisitTree.branch 484 (VisitTree.leaf 483 [273, 273, 273, 273]) (VisitTree.leaf 484 [271])) (VisitTree.branch 502 (VisitTree.leaf 501 [272, 272, 272, 272, 272, 272, 272, 272]) (VisitTree.leaf 502 [273])))))

def fastForwardChunkVisits026 (r : Nat) : List Nat :=
  forwardVisitTree026.lookup r

private theorem covered026 :
    visitsCovered forwardEventChunk026 forwardVisitTree026 = true := by
  decide +kernel

private theorem checked026 :
    visitsChecked forwardEventChunk026 forwardVisitTree026 = true := by
  decide +kernel

theorem eventVisits_forwardChunk026 (r : Nat) :
    eventVisits r forwardEventChunk026 = fastForwardChunkVisits026 r :=
  eventVisits_of_tree _ _ covered026 checked026 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk026

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 27. -/
def forwardVisitTree027 : VisitTree := (VisitTree.branch 421 (VisitTree.branch 304 (VisitTree.branch 288 (VisitTree.leaf 240 [274, 274, 274, 274, 274, 274, 274]) (VisitTree.branch 298 (VisitTree.leaf 288 [274, 274, 274, 274, 274, 274]) (VisitTree.leaf 298 [274, 274, 274, 274, 274, 274]))) (VisitTree.branch 308 (VisitTree.leaf 304 [274, 274, 274, 274, 274, 274]) (VisitTree.branch 419 (VisitTree.leaf 308 [274, 274, 274, 274, 274, 274, 274]) (VisitTree.leaf 419 [273, 273, 273, 273, 273])))) (VisitTree.branch 483 (VisitTree.branch 427 (VisitTree.leaf 421 [273, 273, 273, 273, 273]) (VisitTree.branch 439 (VisitTree.leaf 427 [273, 273, 273, 273, 273]) (VisitTree.leaf 439 [273, 273, 273, 273, 273]))) (VisitTree.branch 500 (VisitTree.leaf 483 [273, 273, 273, 273]) (VisitTree.branch 502 (VisitTree.leaf 500 [274, 274, 274, 274]) (VisitTree.leaf 502 [273, 273, 273, 273])))))

def fastForwardChunkVisits027 (r : Nat) : List Nat :=
  forwardVisitTree027.lookup r

private theorem covered027 :
    visitsCovered forwardEventChunk027 forwardVisitTree027 = true := by
  decide +kernel

private theorem checked027 :
    visitsChecked forwardEventChunk027 forwardVisitTree027 = true := by
  decide +kernel

theorem eventVisits_forwardChunk027 (r : Nat) :
    eventVisits r forwardEventChunk027 = fastForwardChunkVisits027 r :=
  eventVisits_of_tree _ _ covered027 checked027 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk027

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 28. -/
def forwardVisitTree028 : VisitTree := (VisitTree.branch 423 (VisitTree.branch 338 (VisitTree.branch 240 (VisitTree.leaf 232 [276, 276, 276, 276]) (VisitTree.branch 334 (VisitTree.leaf 240 [274]) (VisitTree.leaf 334 [276, 276, 276, 276]))) (VisitTree.branch 346 (VisitTree.branch 342 (VisitTree.leaf 338 [276, 276, 276, 276, 276]) (VisitTree.leaf 342 [276, 276, 276])) (VisitTree.branch 417 (VisitTree.leaf 346 [276, 276, 276, 276, 276]) (VisitTree.leaf 417 [275, 275, 275, 275, 275, 275])))) (VisitTree.branch 482 (VisitTree.branch 425 (VisitTree.leaf 423 [275, 275, 275, 275, 275]) (VisitTree.branch 437 (VisitTree.leaf 425 [275, 275, 275, 275, 275, 275]) (VisitTree.leaf 437 [275, 275, 275, 275, 275, 275, 275]))) (VisitTree.branch 503 (VisitTree.branch 500 (VisitTree.leaf 482 [275, 275, 275, 275, 275, 275, 275]) (VisitTree.leaf 500 [274])) (VisitTree.branch 504 (VisitTree.leaf 503 [275, 275, 275, 275, 275]) (VisitTree.leaf 504 [276, 276, 276, 276, 276])))))

def fastForwardChunkVisits028 (r : Nat) : List Nat :=
  forwardVisitTree028.lookup r

private theorem covered028 :
    visitsCovered forwardEventChunk028 forwardVisitTree028 = true := by
  decide +kernel

private theorem checked028 :
    visitsChecked forwardEventChunk028 forwardVisitTree028 = true := by
  decide +kernel

theorem eventVisits_forwardChunk028 (r : Nat) :
    eventVisits r forwardEventChunk028 = fastForwardChunkVisits028 r :=
  eventVisits_of_tree _ _ covered028 checked028 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk028

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 29. -/
def forwardVisitTree029 : VisitTree := (VisitTree.branch 346 (VisitTree.branch 339 (VisitTree.branch 334 (VisitTree.branch 232 (VisitTree.leaf 231 [278]) (VisitTree.leaf 232 [276, 276, 276])) (VisitTree.branch 338 (VisitTree.leaf 334 [276, 276, 276]) (VisitTree.leaf 338 [276]))) (VisitTree.branch 342 (VisitTree.branch 341 (VisitTree.leaf 339 [278, 278]) (VisitTree.leaf 341 [278, 278, 278, 278])) (VisitTree.branch 343 (VisitTree.leaf 342 [276, 276]) (VisitTree.leaf 343 [278, 278])))) (VisitTree.branch 456 (VisitTree.branch 447 (VisitTree.branch 375 (VisitTree.leaf 346 [276, 276, 276]) (VisitTree.leaf 375 [278, 278, 278])) (VisitTree.branch 455 (VisitTree.leaf 447 [277, 277, 277, 277, 277, 277]) (VisitTree.leaf 455 [277, 277, 277, 277, 277, 277]))) (VisitTree.branch 461 (VisitTree.branch 457 (VisitTree.leaf 456 [278, 278]) (VisitTree.leaf 457 [277, 277, 277, 277, 277, 277, 277])) (VisitTree.branch 481 (VisitTree.leaf 461 [277, 277, 277, 277, 277, 277, 277]) (VisitTree.branch 499 (VisitTree.leaf 481 [277, 277, 277, 277, 277, 277, 277]) (VisitTree.leaf 499 [277, 277, 277, 277, 277]))))))

def fastForwardChunkVisits029 (r : Nat) : List Nat :=
  forwardVisitTree029.lookup r

private theorem covered029 :
    visitsCovered forwardEventChunk029 forwardVisitTree029 = true := by
  decide +kernel

private theorem checked029 :
    visitsChecked forwardEventChunk029 forwardVisitTree029 = true := by
  decide +kernel

theorem eventVisits_forwardChunk029 (r : Nat) :
    eventVisits r forwardEventChunk029 = fastForwardChunkVisits029 r :=
  eventVisits_of_tree _ _ covered029 checked029 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk029

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 30. -/
def forwardVisitTree030 : VisitTree := (VisitTree.branch 343 (VisitTree.branch 331 (VisitTree.branch 249 (VisitTree.leaf 231 [278, 278, 278, 278, 278, 278, 278]) (VisitTree.branch 329 (VisitTree.leaf 249 [279, 279, 279, 279, 279, 279]) (VisitTree.leaf 329 [279, 279, 279, 279, 279]))) (VisitTree.branch 339 (VisitTree.leaf 331 [279, 279, 279, 279, 279, 279]) (VisitTree.branch 341 (VisitTree.leaf 339 [278, 278, 278, 278, 278]) (VisitTree.leaf 341 [278, 278, 278, 278])))) (VisitTree.branch 449 (VisitTree.branch 354 (VisitTree.leaf 343 [278, 278, 278, 278, 278]) (VisitTree.branch 375 (VisitTree.leaf 354 [279, 279, 279, 279, 279]) (VisitTree.leaf 375 [278, 278, 278, 278, 278]))) (VisitTree.branch 456 (VisitTree.leaf 449 [279, 279, 279, 279, 279, 279]) (VisitTree.branch 492 (VisitTree.leaf 456 [278, 278, 278, 278]) (VisitTree.leaf 492 [279, 279, 279, 279, 279, 279])))))

def fastForwardChunkVisits030 (r : Nat) : List Nat :=
  forwardVisitTree030.lookup r

private theorem covered030 :
    visitsCovered forwardEventChunk030 forwardVisitTree030 = true := by
  decide +kernel

private theorem checked030 :
    visitsChecked forwardEventChunk030 forwardVisitTree030 = true := by
  decide +kernel

theorem eventVisits_forwardChunk030 (r : Nat) :
    eventVisits r forwardEventChunk030 = fastForwardChunkVisits030 r :=
  eventVisits_of_tree _ _ covered030 checked030 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk030

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 31. -/
def forwardVisitTree031 : VisitTree := (VisitTree.branch 329 (VisitTree.branch 281 (VisitTree.branch 263 (VisitTree.leaf 261 [280, 280, 280, 280, 280, 280, 280]) (VisitTree.branch 275 (VisitTree.leaf 263 [281]) (VisitTree.leaf 275 [281, 281]))) (VisitTree.branch 309 (VisitTree.branch 299 (VisitTree.leaf 281 [280, 280, 280, 280, 280, 280, 280, 280]) (VisitTree.leaf 299 [280, 280, 280, 280, 280, 280, 280])) (VisitTree.branch 310 (VisitTree.leaf 309 [280, 280, 280, 280, 280, 280, 280, 280]) (VisitTree.leaf 310 [281, 281, 281])))) (VisitTree.branch 380 (VisitTree.branch 345 (VisitTree.branch 331 (VisitTree.leaf 329 [279]) (VisitTree.leaf 331 [279, 279])) (VisitTree.branch 374 (VisitTree.leaf 345 [280, 280, 280, 280, 280, 280, 280, 280]) (VisitTree.leaf 374 [281, 281]))) (VisitTree.branch 491 (VisitTree.branch 410 (VisitTree.leaf 380 [280, 280, 280, 280, 280, 280, 280, 280]) (VisitTree.leaf 410 [281, 281])) (VisitTree.branch 492 (VisitTree.leaf 491 [281, 281, 281, 281]) (VisitTree.leaf 492 [279])))))

def fastForwardChunkVisits031 (r : Nat) : List Nat :=
  forwardVisitTree031.lookup r

private theorem covered031 :
    visitsCovered forwardEventChunk031 forwardVisitTree031 = true := by
  decide +kernel

private theorem checked031 :
    visitsChecked forwardEventChunk031 forwardVisitTree031 = true := by
  decide +kernel

theorem eventVisits_forwardChunk031 (r : Nat) :
    eventVisits r forwardEventChunk031 = fastForwardChunkVisits031 r :=
  eventVisits_of_tree _ _ covered031 checked031 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk031

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 32. -/
def forwardVisitTree032 : VisitTree := (VisitTree.branch 374 (VisitTree.branch 310 (VisitTree.branch 263 (VisitTree.leaf 256 [282, 282, 282, 282, 282, 282, 282]) (VisitTree.branch 275 (VisitTree.leaf 263 [281, 281, 281, 281, 281]) (VisitTree.leaf 275 [281, 281, 281, 281]))) (VisitTree.branch 325 (VisitTree.leaf 310 [281, 281, 281, 281, 281]) (VisitTree.branch 359 (VisitTree.leaf 325 [282, 282, 282, 282, 282, 282, 282]) (VisitTree.leaf 359 [282, 282, 282, 282])))) (VisitTree.branch 410 (VisitTree.branch 392 (VisitTree.leaf 374 [281, 281, 281, 281]) (VisitTree.branch 404 (VisitTree.leaf 392 [282, 282, 282, 282, 282, 282]) (VisitTree.leaf 404 [282, 282, 282, 282, 282, 282]))) (VisitTree.branch 442 (VisitTree.leaf 410 [281, 281, 281, 281, 281, 281]) (VisitTree.branch 491 (VisitTree.leaf 442 [282, 282, 282, 282, 282, 282]) (VisitTree.leaf 491 [281, 281, 281, 281])))))

def fastForwardChunkVisits032 (r : Nat) : List Nat :=
  forwardVisitTree032.lookup r

private theorem covered032 :
    visitsCovered forwardEventChunk032 forwardVisitTree032 = true := by
  decide +kernel

private theorem checked032 :
    visitsChecked forwardEventChunk032 forwardVisitTree032 = true := by
  decide +kernel

theorem eventVisits_forwardChunk032 (r : Nat) :
    eventVisits r forwardEventChunk032 = fastForwardChunkVisits032 r :=
  eventVisits_of_tree _ _ covered032 checked032 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk032

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 33. -/
def forwardVisitTree033 : VisitTree := (VisitTree.branch 400 (VisitTree.branch 344 (VisitTree.branch 312 (VisitTree.leaf 283 [284, 284, 284]) (VisitTree.branch 325 (VisitTree.leaf 312 [283, 283, 283, 283, 283, 283, 283]) (VisitTree.leaf 325 [282]))) (VisitTree.branch 359 (VisitTree.branch 355 (VisitTree.leaf 344 [284, 284, 284, 284, 284]) (VisitTree.leaf 355 [283, 283, 283, 283, 283, 283])) (VisitTree.branch 390 (VisitTree.leaf 359 [282]) (VisitTree.leaf 390 [284, 284, 284, 284, 284])))) (VisitTree.branch 429 (VisitTree.branch 412 (VisitTree.leaf 400 [284, 284, 284, 284, 284]) (VisitTree.branch 418 (VisitTree.leaf 412 [283, 283, 283, 283, 283]) (VisitTree.leaf 418 [284, 284, 284, 284, 284]))) (VisitTree.branch 490 (VisitTree.branch 434 (VisitTree.leaf 429 [283, 283, 283, 283, 283]) (VisitTree.leaf 434 [283, 283, 283, 283, 283])) (VisitTree.branch 508 (VisitTree.leaf 490 [283, 283, 283, 283, 283, 283, 283, 283]) (VisitTree.leaf 508 [284, 284, 284])))))

def fastForwardChunkVisits033 (r : Nat) : List Nat :=
  forwardVisitTree033.lookup r

private theorem covered033 :
    visitsCovered forwardEventChunk033 forwardVisitTree033 = true := by
  decide +kernel

private theorem checked033 :
    visitsChecked forwardEventChunk033 forwardVisitTree033 = true := by
  decide +kernel

theorem eventVisits_forwardChunk033 (r : Nat) :
    eventVisits r forwardEventChunk033 = fastForwardChunkVisits033 r :=
  eventVisits_of_tree _ _ covered033 checked033 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk033

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 34. -/
def forwardVisitTree034 : VisitTree := (VisitTree.branch 418 (VisitTree.branch 390 (VisitTree.branch 344 (VisitTree.leaf 283 [284, 284, 284]) (VisitTree.branch 383 (VisitTree.leaf 344 [284, 284, 284]) (VisitTree.leaf 383 [285, 285, 285, 285, 285, 285, 285, 285]))) (VisitTree.branch 400 (VisitTree.leaf 390 [284, 284, 284]) (VisitTree.branch 408 (VisitTree.leaf 400 [284, 284, 284]) (VisitTree.leaf 408 [285, 285, 285, 285, 285, 285, 285, 285])))) (VisitTree.branch 489 (VisitTree.branch 426 (VisitTree.leaf 418 [284]) (VisitTree.branch 431 (VisitTree.leaf 426 [285, 285, 285, 285, 285, 285, 285, 285]) (VisitTree.leaf 431 [285, 285, 285, 285, 285, 285, 285, 285]))) (VisitTree.branch 507 (VisitTree.leaf 489 [285, 285, 285, 285, 285, 285, 285, 285]) (VisitTree.branch 508 (VisitTree.leaf 507 [285, 285, 285, 285, 285, 285, 285, 285]) (VisitTree.leaf 508 [284, 284, 284])))))

def fastForwardChunkVisits034 (r : Nat) : List Nat :=
  forwardVisitTree034.lookup r

private theorem covered034 :
    visitsCovered forwardEventChunk034 forwardVisitTree034 = true := by
  decide +kernel

private theorem checked034 :
    visitsChecked forwardEventChunk034 forwardVisitTree034 = true := by
  decide +kernel

theorem eventVisits_forwardChunk034 (r : Nat) :
    eventVisits r forwardEventChunk034 = fastForwardChunkVisits034 r :=
  eventVisits_of_tree _ _ covered034 checked034 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk034

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 35. -/
def forwardVisitTree035 : VisitTree := (VisitTree.branch 318 (VisitTree.branch 300 (VisitTree.branch 270 (VisitTree.leaf 265 [287, 287, 287, 287]) (VisitTree.branch 286 (VisitTree.leaf 270 [287, 287, 287, 287]) (VisitTree.leaf 286 [287, 287, 287]))) (VisitTree.branch 305 (VisitTree.leaf 300 [286, 286, 286, 286, 286, 286, 286]) (VisitTree.branch 315 (VisitTree.leaf 305 [286, 286, 286, 286, 286, 286, 286]) (VisitTree.leaf 315 [287, 287, 287, 287])))) (VisitTree.branch 488 (VisitTree.branch 414 (VisitTree.leaf 318 [286, 286, 286, 286, 286, 286, 286]) (VisitTree.branch 441 (VisitTree.leaf 414 [286, 286, 286, 286, 286, 286, 286]) (VisitTree.leaf 441 [286, 286, 286, 286, 286, 286, 286]))) (VisitTree.branch 506 (VisitTree.leaf 488 [287, 287, 287, 287, 287]) (VisitTree.branch 509 (VisitTree.leaf 506 [287, 287, 287, 287]) (VisitTree.leaf 509 [286, 286, 286, 286, 286])))))

def fastForwardChunkVisits035 (r : Nat) : List Nat :=
  forwardVisitTree035.lookup r

private theorem covered035 :
    visitsCovered forwardEventChunk035 forwardVisitTree035 = true := by
  decide +kernel

private theorem checked035 :
    visitsChecked forwardEventChunk035 forwardVisitTree035 = true := by
  decide +kernel

theorem eventVisits_forwardChunk035 (r : Nat) :
    eventVisits r forwardEventChunk035 = fastForwardChunkVisits035 r :=
  eventVisits_of_tree _ _ covered035 checked035 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk035


