-- Prove2me | Definitions.Def_CSL_Generated_MemoryAccess_Group10
-- name    : CSL_Generated_MemoryAccess_Group10
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T13:31:10.726836+00:00
-- url     : https://prove2.me/theorems/580f7275-a6e2-49e3-9f8b-06b6fde6e461
-- title:
--   Coded sorting library: Generated / MemoryAccess / Group10
-- statement:
--   Module `CodedSorting.Generated.MemoryAccess.Group10` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Generated.MemoryAccess.Group10

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Circuit_MemoryAccess_PhysicalFrameEventChunkData
import Definitions.Def_CSL_Generated_MemoryAccess_Base

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 164. -/
def forwardVisitTree164 : VisitTree := (VisitTree.branch 379 (VisitTree.branch 270 (VisitTree.branch 64 (VisitTree.branch 38 (VisitTree.branch 22 (VisitTree.leaf 17 [1]) (VisitTree.branch 33 (VisitTree.leaf 22 [1]) (VisitTree.leaf 33 [1]))) (VisitTree.branch 51 (VisitTree.leaf 38 [1]) (VisitTree.branch 55 (VisitTree.leaf 51 [1]) (VisitTree.leaf 55 [1])))) (VisitTree.branch 92 (VisitTree.branch 71 (VisitTree.leaf 64 [1]) (VisitTree.branch 77 (VisitTree.leaf 71 [1]) (VisitTree.leaf 77 [1]))) (VisitTree.branch 260 (VisitTree.leaf 92 [1]) (VisitTree.branch 261 (VisitTree.leaf 260 [1, 1]) (VisitTree.leaf 261 [1]))))) (VisitTree.branch 332 (VisitTree.branch 293 (VisitTree.branch 271 (VisitTree.leaf 270 [1, 1]) (VisitTree.branch 292 (VisitTree.leaf 271 [1]) (VisitTree.leaf 292 [1, 1]))) (VisitTree.branch 302 (VisitTree.leaf 293 [1]) (VisitTree.branch 315 (VisitTree.leaf 302 [1, 1]) (VisitTree.leaf 315 [1])))) (VisitTree.branch 343 (VisitTree.branch 333 (VisitTree.leaf 332 [1]) (VisitTree.branch 342 (VisitTree.leaf 333 [1]) (VisitTree.leaf 342 [1, 1]))) (VisitTree.branch 363 (VisitTree.branch 362 (VisitTree.leaf 343 [1, 1]) (VisitTree.leaf 362 [1, 1])) (VisitTree.branch 378 (VisitTree.leaf 363 [1, 1]) (VisitTree.leaf 378 [1, 1])))))) (VisitTree.branch 567 (VisitTree.branch 423 (VisitTree.branch 407 (VisitTree.branch 390 (VisitTree.leaf 379 [1, 1]) (VisitTree.branch 397 (VisitTree.leaf 390 [1]) (VisitTree.leaf 397 [1, 1]))) (VisitTree.branch 412 (VisitTree.leaf 407 [1]) (VisitTree.branch 422 (VisitTree.leaf 412 [1, 1]) (VisitTree.leaf 422 [1, 1])))) (VisitTree.branch 564 (VisitTree.branch 445 (VisitTree.leaf 423 [1]) (VisitTree.branch 563 (VisitTree.leaf 445 [1, 1]) (VisitTree.leaf 563 [1]))) (VisitTree.branch 565 (VisitTree.leaf 564 [1]) (VisitTree.branch 566 (VisitTree.leaf 565 [1]) (VisitTree.leaf 566 [1]))))) (VisitTree.branch 573 (VisitTree.branch 570 (VisitTree.branch 568 (VisitTree.leaf 567 [1]) (VisitTree.branch 569 (VisitTree.leaf 568 [1]) (VisitTree.leaf 569 [1]))) (VisitTree.branch 571 (VisitTree.leaf 570 [1]) (VisitTree.branch 572 (VisitTree.leaf 571 [1]) (VisitTree.leaf 572 [1])))) (VisitTree.branch 576 (VisitTree.branch 574 (VisitTree.leaf 573 [1]) (VisitTree.branch 575 (VisitTree.leaf 574 [1]) (VisitTree.leaf 575 [1]))) (VisitTree.branch 578 (VisitTree.branch 577 (VisitTree.leaf 576 [1]) (VisitTree.leaf 577 [1])) (VisitTree.branch 579 (VisitTree.leaf 578 [1]) (VisitTree.leaf 579 [1])))))))

def fastForwardChunkVisits164 (r : Nat) : List Nat :=
  forwardVisitTree164.lookup r

private theorem covered164 :
    visitsCovered forwardEventChunk164 forwardVisitTree164 = true := by
  decide +kernel

private theorem checked164 :
    visitsChecked forwardEventChunk164 forwardVisitTree164 = true := by
  decide +kernel

theorem eventVisits_forwardChunk164 (r : Nat) :
    eventVisits r forwardEventChunk164 = fastForwardChunkVisits164 r :=
  eventVisits_of_tree _ _ covered164 checked164 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk164

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 165. -/
def forwardVisitTree165 : VisitTree := (VisitTree.branch 365 (VisitTree.branch 269 (VisitTree.branch 66 (VisitTree.branch 44 (VisitTree.branch 26 (VisitTree.leaf 21 [1]) (VisitTree.branch 36 (VisitTree.leaf 26 [1]) (VisitTree.leaf 36 [1]))) (VisitTree.branch 57 (VisitTree.leaf 44 [1]) (VisitTree.branch 65 (VisitTree.leaf 57 [1]) (VisitTree.leaf 65 [1])))) (VisitTree.branch 94 (VisitTree.branch 80 (VisitTree.leaf 66 [1]) (VisitTree.branch 84 (VisitTree.leaf 80 [1]) (VisitTree.leaf 84 [1]))) (VisitTree.branch 102 (VisitTree.leaf 94 [1]) (VisitTree.branch 268 (VisitTree.leaf 102 [1]) (VisitTree.leaf 268 [1, 1]))))) (VisitTree.branch 315 (VisitTree.branch 298 (VisitTree.branch 278 (VisitTree.leaf 269 [1, 1]) (VisitTree.branch 279 (VisitTree.leaf 278 [1]) (VisitTree.leaf 279 [1, 1]))) (VisitTree.branch 299 (VisitTree.leaf 298 [1, 1]) (VisitTree.branch 314 (VisitTree.leaf 299 [1, 1]) (VisitTree.leaf 314 [1, 1])))) (VisitTree.branch 346 (VisitTree.branch 328 (VisitTree.leaf 315 [1]) (VisitTree.branch 329 (VisitTree.leaf 328 [1, 1]) (VisitTree.leaf 329 [1, 1]))) (VisitTree.branch 347 (VisitTree.leaf 346 [1]) (VisitTree.branch 364 (VisitTree.leaf 347 [1, 1]) (VisitTree.leaf 364 [1, 1])))))) (VisitTree.branch 550 (VisitTree.branch 427 (VisitTree.branch 396 (VisitTree.branch 368 (VisitTree.leaf 365 [1]) (VisitTree.branch 369 (VisitTree.leaf 368 [1]) (VisitTree.leaf 369 [1, 1]))) (VisitTree.branch 406 (VisitTree.leaf 396 [1]) (VisitTree.branch 426 (VisitTree.leaf 406 [1, 1]) (VisitTree.leaf 426 [1, 1])))) (VisitTree.branch 547 (VisitTree.branch 442 (VisitTree.leaf 427 [1, 1]) (VisitTree.branch 443 (VisitTree.leaf 442 [1, 1]) (VisitTree.leaf 443 [1]))) (VisitTree.branch 548 (VisitTree.leaf 547 [1]) (VisitTree.branch 549 (VisitTree.leaf 548 [1]) (VisitTree.leaf 549 [1]))))) (VisitTree.branch 556 (VisitTree.branch 553 (VisitTree.branch 551 (VisitTree.leaf 550 [1]) (VisitTree.branch 552 (VisitTree.leaf 551 [1]) (VisitTree.leaf 552 [1]))) (VisitTree.branch 554 (VisitTree.leaf 553 [1]) (VisitTree.branch 555 (VisitTree.leaf 554 [1]) (VisitTree.leaf 555 [1])))) (VisitTree.branch 559 (VisitTree.branch 557 (VisitTree.leaf 556 [1]) (VisitTree.branch 558 (VisitTree.leaf 557 [1]) (VisitTree.leaf 558 [1]))) (VisitTree.branch 561 (VisitTree.branch 560 (VisitTree.leaf 559 [1]) (VisitTree.leaf 560 [1])) (VisitTree.branch 562 (VisitTree.leaf 561 [1]) (VisitTree.leaf 562 [1])))))))

def fastForwardChunkVisits165 (r : Nat) : List Nat :=
  forwardVisitTree165.lookup r

private theorem covered165 :
    visitsCovered forwardEventChunk165 forwardVisitTree165 = true := by
  decide +kernel

private theorem checked165 :
    visitsChecked forwardEventChunk165 forwardVisitTree165 = true := by
  decide +kernel

theorem eventVisits_forwardChunk165 (r : Nat) :
    eventVisits r forwardEventChunk165 = fastForwardChunkVisits165 r :=
  eventVisits_of_tree _ _ covered165 checked165 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk165

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 166. -/
def forwardVisitTree166 : VisitTree := (VisitTree.branch 384 (VisitTree.branch 281 (VisitTree.branch 74 (VisitTree.branch 43 (VisitTree.branch 27 (VisitTree.leaf 19 [1]) (VisitTree.branch 35 (VisitTree.leaf 27 [1]) (VisitTree.leaf 35 [1]))) (VisitTree.branch 53 (VisitTree.leaf 43 [1]) (VisitTree.branch 70 (VisitTree.leaf 53 [1]) (VisitTree.leaf 70 [1])))) (VisitTree.branch 264 (VisitTree.branch 89 (VisitTree.leaf 74 [1]) (VisitTree.branch 97 (VisitTree.leaf 89 [1]) (VisitTree.leaf 97 [1]))) (VisitTree.branch 265 (VisitTree.leaf 264 [1, 1]) (VisitTree.branch 280 (VisitTree.leaf 265 [1, 1]) (VisitTree.leaf 280 [1, 1]))))) (VisitTree.branch 327 (VisitTree.branch 312 (VisitTree.branch 296 (VisitTree.leaf 281 [1, 1]) (VisitTree.branch 297 (VisitTree.leaf 296 [1, 1]) (VisitTree.leaf 297 [1]))) (VisitTree.branch 313 (VisitTree.leaf 312 [1, 1]) (VisitTree.branch 326 (VisitTree.leaf 313 [1]) (VisitTree.leaf 326 [1])))) (VisitTree.branch 351 (VisitTree.branch 339 (VisitTree.leaf 327 [1]) (VisitTree.branch 350 (VisitTree.leaf 339 [1, 1]) (VisitTree.leaf 350 [1, 1]))) (VisitTree.branch 376 (VisitTree.leaf 351 [1, 1]) (VisitTree.branch 377 (VisitTree.leaf 376 [1, 1]) (VisitTree.leaf 377 [1])))))) (VisitTree.branch 534 (VisitTree.branch 432 (VisitTree.branch 401 (VisitTree.branch 385 (VisitTree.leaf 384 [1, 1]) (VisitTree.branch 400 (VisitTree.leaf 385 [1]) (VisitTree.leaf 400 [1, 1]))) (VisitTree.branch 416 (VisitTree.leaf 401 [1, 1]) (VisitTree.branch 417 (VisitTree.leaf 416 [1]) (VisitTree.leaf 417 [1, 1])))) (VisitTree.branch 531 (VisitTree.branch 433 (VisitTree.leaf 432 [1, 1]) (VisitTree.branch 530 (VisitTree.leaf 433 [1]) (VisitTree.leaf 530 [1]))) (VisitTree.branch 532 (VisitTree.leaf 531 [1]) (VisitTree.branch 533 (VisitTree.leaf 532 [1]) (VisitTree.leaf 533 [1]))))) (VisitTree.branch 540 (VisitTree.branch 537 (VisitTree.branch 535 (VisitTree.leaf 534 [1]) (VisitTree.branch 536 (VisitTree.leaf 535 [1]) (VisitTree.leaf 536 [1]))) (VisitTree.branch 538 (VisitTree.leaf 537 [1]) (VisitTree.branch 539 (VisitTree.leaf 538 [1]) (VisitTree.leaf 539 [1])))) (VisitTree.branch 543 (VisitTree.branch 541 (VisitTree.leaf 540 [1]) (VisitTree.branch 542 (VisitTree.leaf 541 [1]) (VisitTree.leaf 542 [1]))) (VisitTree.branch 545 (VisitTree.branch 544 (VisitTree.leaf 543 [1]) (VisitTree.leaf 544 [1])) (VisitTree.branch 546 (VisitTree.leaf 545 [1]) (VisitTree.leaf 546 [1])))))))

def fastForwardChunkVisits166 (r : Nat) : List Nat :=
  forwardVisitTree166.lookup r

private theorem covered166 :
    visitsCovered forwardEventChunk166 forwardVisitTree166 = true := by
  decide +kernel

private theorem checked166 :
    visitsChecked forwardEventChunk166 forwardVisitTree166 = true := by
  decide +kernel

theorem eventVisits_forwardChunk166 (r : Nat) :
    eventVisits r forwardEventChunk166 = fastForwardChunkVisits166 r :=
  eventVisits_of_tree _ _ covered166 checked166 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk166

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 167. -/
def forwardVisitTree167 : VisitTree := (VisitTree.branch 373 (VisitTree.branch 257 (VisitTree.branch 68 (VisitTree.branch 41 (VisitTree.branch 23 (VisitTree.leaf 15 [1]) (VisitTree.branch 30 (VisitTree.leaf 23 [1]) (VisitTree.leaf 30 [1]))) (VisitTree.branch 49 (VisitTree.leaf 41 [1]) (VisitTree.branch 59 (VisitTree.leaf 49 [1]) (VisitTree.leaf 59 [1])))) (VisitTree.branch 91 (VisitTree.branch 75 (VisitTree.leaf 68 [1]) (VisitTree.branch 82 (VisitTree.leaf 75 [1]) (VisitTree.leaf 82 [1]))) (VisitTree.branch 96 (VisitTree.leaf 91 [1]) (VisitTree.branch 256 (VisitTree.leaf 96 [1]) (VisitTree.leaf 256 [1, 1]))))) (VisitTree.branch 309 (VisitTree.branch 286 (VisitTree.branch 272 (VisitTree.leaf 257 [1]) (VisitTree.branch 273 (VisitTree.leaf 272 [1, 1]) (VisitTree.leaf 273 [1]))) (VisitTree.branch 287 (VisitTree.leaf 286 [1, 1]) (VisitTree.branch 308 (VisitTree.leaf 287 [1]) (VisitTree.leaf 308 [1, 1])))) (VisitTree.branch 360 (VisitTree.branch 326 (VisitTree.leaf 309 [1, 1]) (VisitTree.branch 338 (VisitTree.leaf 326 [1]) (VisitTree.leaf 338 [1, 1]))) (VisitTree.branch 361 (VisitTree.leaf 360 [1]) (VisitTree.branch 367 (VisitTree.leaf 361 [1, 1]) (VisitTree.leaf 367 [1, 1])))))) (VisitTree.branch 517 (VisitTree.branch 421 (VisitTree.branch 402 (VisitTree.branch 386 (VisitTree.leaf 373 [1]) (VisitTree.branch 387 (VisitTree.leaf 386 [1]) (VisitTree.leaf 387 [1, 1]))) (VisitTree.branch 403 (VisitTree.leaf 402 [1, 1]) (VisitTree.branch 420 (VisitTree.leaf 403 [1, 1]) (VisitTree.leaf 420 [1, 1])))) (VisitTree.branch 514 (VisitTree.branch 430 (VisitTree.leaf 421 [1, 1]) (VisitTree.branch 431 (VisitTree.leaf 430 [1, 1]) (VisitTree.leaf 431 [1, 1]))) (VisitTree.branch 515 (VisitTree.leaf 514 [1]) (VisitTree.branch 516 (VisitTree.leaf 515 [1]) (VisitTree.leaf 516 [1]))))) (VisitTree.branch 523 (VisitTree.branch 520 (VisitTree.branch 518 (VisitTree.leaf 517 [1]) (VisitTree.branch 519 (VisitTree.leaf 518 [1]) (VisitTree.leaf 519 [1]))) (VisitTree.branch 521 (VisitTree.leaf 520 [1]) (VisitTree.branch 522 (VisitTree.leaf 521 [1]) (VisitTree.leaf 522 [1])))) (VisitTree.branch 526 (VisitTree.branch 524 (VisitTree.leaf 523 [1]) (VisitTree.branch 525 (VisitTree.leaf 524 [1]) (VisitTree.leaf 525 [1]))) (VisitTree.branch 528 (VisitTree.branch 527 (VisitTree.leaf 526 [1]) (VisitTree.leaf 527 [1])) (VisitTree.branch 529 (VisitTree.leaf 528 [1]) (VisitTree.leaf 529 [1])))))))

def fastForwardChunkVisits167 (r : Nat) : List Nat :=
  forwardVisitTree167.lookup r

private theorem covered167 :
    visitsCovered forwardEventChunk167 forwardVisitTree167 = true := by
  decide +kernel

private theorem checked167 :
    visitsChecked forwardEventChunk167 forwardVisitTree167 = true := by
  decide +kernel

theorem eventVisits_forwardChunk167 (r : Nat) :
    eventVisits r forwardEventChunk167 = fastForwardChunkVisits167 r :=
  eventVisits_of_tree _ _ covered167 checked167 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk167

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 168. -/
def forwardVisitTree168 : VisitTree := (VisitTree.branch 358 (VisitTree.branch 229 (VisitTree.branch 63 (VisitTree.branch 58 (VisitTree.branch 3 (VisitTree.leaf 0 [1]) (VisitTree.branch 11 (VisitTree.leaf 3 [1]) (VisitTree.leaf 11 [1]))) (VisitTree.branch 61 (VisitTree.leaf 58 [1]) (VisitTree.branch 62 (VisitTree.leaf 61 [1]) (VisitTree.leaf 62 [1])))) (VisitTree.branch 222 (VisitTree.branch 69 (VisitTree.leaf 63 [1]) (VisitTree.branch 72 (VisitTree.leaf 69 [1]) (VisitTree.leaf 72 [1]))) (VisitTree.branch 223 (VisitTree.leaf 222 [1, 1]) (VisitTree.branch 228 (VisitTree.leaf 223 [1, 1]) (VisitTree.leaf 228 [1]))))) (VisitTree.branch 337 (VisitTree.branch 252 (VisitTree.branch 246 (VisitTree.leaf 229 [1]) (VisitTree.branch 247 (VisitTree.leaf 246 [1, 1]) (VisitTree.leaf 247 [1]))) (VisitTree.branch 253 (VisitTree.leaf 252 [1, 1]) (VisitTree.branch 323 (VisitTree.leaf 253 [1, 1]) (VisitTree.leaf 323 [1, 1])))) (VisitTree.branch 355 (VisitTree.branch 349 (VisitTree.leaf 337 [1, 1]) (VisitTree.branch 354 (VisitTree.leaf 349 [1]) (VisitTree.leaf 354 [1, 1]))) (VisitTree.branch 356 (VisitTree.leaf 355 [1, 1]) (VisitTree.branch 357 (VisitTree.leaf 356 [1, 1]) (VisitTree.leaf 357 [1])))))) (VisitTree.branch 501 (VisitTree.branch 380 (VisitTree.branch 372 (VisitTree.branch 359 (VisitTree.leaf 358 [1]) (VisitTree.branch 366 (VisitTree.leaf 359 [1, 1]) (VisitTree.leaf 366 [1, 1]))) (VisitTree.branch 374 (VisitTree.leaf 372 [1, 1]) (VisitTree.branch 375 (VisitTree.leaf 374 [1]) (VisitTree.leaf 375 [1, 1])))) (VisitTree.branch 498 (VisitTree.branch 381 (VisitTree.leaf 380 [1, 1]) (VisitTree.branch 497 (VisitTree.leaf 381 [1]) (VisitTree.leaf 497 [1]))) (VisitTree.branch 499 (VisitTree.leaf 498 [1]) (VisitTree.branch 500 (VisitTree.leaf 499 [1]) (VisitTree.leaf 500 [1]))))) (VisitTree.branch 507 (VisitTree.branch 504 (VisitTree.branch 502 (VisitTree.leaf 501 [1]) (VisitTree.branch 503 (VisitTree.leaf 502 [1]) (VisitTree.leaf 503 [1]))) (VisitTree.branch 505 (VisitTree.leaf 504 [1]) (VisitTree.branch 506 (VisitTree.leaf 505 [1]) (VisitTree.leaf 506 [1])))) (VisitTree.branch 510 (VisitTree.branch 508 (VisitTree.leaf 507 [1]) (VisitTree.branch 509 (VisitTree.leaf 508 [1]) (VisitTree.leaf 509 [1]))) (VisitTree.branch 512 (VisitTree.branch 511 (VisitTree.leaf 510 [1]) (VisitTree.leaf 511 [1])) (VisitTree.branch 513 (VisitTree.leaf 512 [1]) (VisitTree.leaf 513 [1])))))))

def fastForwardChunkVisits168 (r : Nat) : List Nat :=
  forwardVisitTree168.lookup r

private theorem covered168 :
    visitsCovered forwardEventChunk168 forwardVisitTree168 = true := by
  decide +kernel

private theorem checked168 :
    visitsChecked forwardEventChunk168 forwardVisitTree168 = true := by
  decide +kernel

theorem eventVisits_forwardChunk168 (r : Nat) :
    eventVisits r forwardEventChunk168 = fastForwardChunkVisits168 r :=
  eventVisits_of_tree _ _ covered168 checked168 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk168

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 169. -/
def forwardVisitTree169 : VisitTree := (VisitTree.branch 325 (VisitTree.branch 233 (VisitTree.branch 47 (VisitTree.branch 17 (VisitTree.branch 6 (VisitTree.leaf 5 [1]) (VisitTree.branch 9 (VisitTree.leaf 6 [1]) (VisitTree.leaf 9 [1]))) (VisitTree.branch 43 (VisitTree.leaf 17 [1]) (VisitTree.branch 46 (VisitTree.leaf 43 [1]) (VisitTree.leaf 46 [1])))) (VisitTree.branch 54 (VisitTree.branch 48 (VisitTree.leaf 47 [1]) (VisitTree.branch 52 (VisitTree.leaf 48 [1]) (VisitTree.leaf 52 [1]))) (VisitTree.branch 56 (VisitTree.leaf 54 [1]) (VisitTree.branch 232 (VisitTree.leaf 56 [1]) (VisitTree.leaf 232 [1, 1]))))) (VisitTree.branch 243 (VisitTree.branch 240 (VisitTree.branch 234 (VisitTree.leaf 233 [1]) (VisitTree.branch 235 (VisitTree.leaf 234 [1, 1]) (VisitTree.leaf 235 [1]))) (VisitTree.branch 241 (VisitTree.leaf 240 [1, 1]) (VisitTree.branch 242 (VisitTree.leaf 241 [1]) (VisitTree.leaf 242 [1, 1])))) (VisitTree.branch 320 (VisitTree.branch 318 (VisitTree.leaf 243 [1, 1]) (VisitTree.branch 319 (VisitTree.leaf 318 [1, 1]) (VisitTree.leaf 319 [1]))) (VisitTree.branch 322 (VisitTree.branch 321 (VisitTree.leaf 320 [1, 1]) (VisitTree.leaf 321 [1, 1])) (VisitTree.branch 324 (VisitTree.leaf 322 [1]) (VisitTree.leaf 324 [1, 1])))))) (VisitTree.branch 484 (VisitTree.branch 348 (VisitTree.branch 341 (VisitTree.branch 336 (VisitTree.leaf 325 [1, 1]) (VisitTree.branch 340 (VisitTree.leaf 336 [1, 1]) (VisitTree.leaf 340 [1]))) (VisitTree.branch 344 (VisitTree.leaf 341 [1, 1]) (VisitTree.branch 345 (VisitTree.leaf 344 [1, 1]) (VisitTree.leaf 345 [1])))) (VisitTree.branch 481 (VisitTree.branch 479 (VisitTree.leaf 348 [1, 1]) (VisitTree.branch 480 (VisitTree.leaf 479 [1]) (VisitTree.leaf 480 [1]))) (VisitTree.branch 482 (VisitTree.leaf 481 [1]) (VisitTree.branch 483 (VisitTree.leaf 482 [1]) (VisitTree.leaf 483 [1]))))) (VisitTree.branch 490 (VisitTree.branch 487 (VisitTree.branch 485 (VisitTree.leaf 484 [1]) (VisitTree.branch 486 (VisitTree.leaf 485 [1]) (VisitTree.leaf 486 [1]))) (VisitTree.branch 488 (VisitTree.leaf 487 [1]) (VisitTree.branch 489 (VisitTree.leaf 488 [1]) (VisitTree.leaf 489 [1])))) (VisitTree.branch 493 (VisitTree.branch 491 (VisitTree.leaf 490 [1]) (VisitTree.branch 492 (VisitTree.leaf 491 [1]) (VisitTree.leaf 492 [1]))) (VisitTree.branch 495 (VisitTree.branch 494 (VisitTree.leaf 493 [1]) (VisitTree.leaf 494 [1])) (VisitTree.branch 496 (VisitTree.leaf 495 [1]) (VisitTree.leaf 496 [1])))))))

def fastForwardChunkVisits169 (r : Nat) : List Nat :=
  forwardVisitTree169.lookup r

private theorem covered169 :
    visitsCovered forwardEventChunk169 forwardVisitTree169 = true := by
  decide +kernel

private theorem checked169 :
    visitsChecked forwardEventChunk169 forwardVisitTree169 = true := by
  decide +kernel

theorem eventVisits_forwardChunk169 (r : Nat) :
    eventVisits r forwardEventChunk169 = fastForwardChunkVisits169 r :=
  eventVisits_of_tree _ _ covered169 checked169 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk169

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 170. -/
def forwardVisitTree170 : VisitTree := (VisitTree.branch 450 (VisitTree.branch 69 (VisitTree.branch 50 (VisitTree.branch 19 (VisitTree.branch 6 (VisitTree.leaf 0 [1]) (VisitTree.branch 11 (VisitTree.leaf 6 [1]) (VisitTree.leaf 11 [1]))) (VisitTree.branch 38 (VisitTree.branch 27 (VisitTree.leaf 19 [1]) (VisitTree.leaf 27 [1])) (VisitTree.branch 47 (VisitTree.leaf 38 [1]) (VisitTree.leaf 47 [1])))) (VisitTree.branch 56 (VisitTree.branch 52 (VisitTree.leaf 50 [1]) (VisitTree.branch 54 (VisitTree.leaf 52 [1]) (VisitTree.leaf 54 [1]))) (VisitTree.branch 67 (VisitTree.branch 57 (VisitTree.leaf 56 [1]) (VisitTree.leaf 57 [1])) (VisitTree.branch 68 (VisitTree.leaf 67 [1]) (VisitTree.leaf 68 [1]))))) (VisitTree.branch 107 (VisitTree.branch 103 (VisitTree.branch 77 (VisitTree.leaf 69 [1]) (VisitTree.branch 92 (VisitTree.leaf 77 [1]) (VisitTree.leaf 92 [1]))) (VisitTree.branch 105 (VisitTree.branch 104 (VisitTree.leaf 103 [1]) (VisitTree.leaf 104 [1, 1])) (VisitTree.branch 106 (VisitTree.leaf 105 [1, 1]) (VisitTree.leaf 106 [1, 1])))) (VisitTree.branch 110 (VisitTree.branch 108 (VisitTree.leaf 107 [1, 1]) (VisitTree.branch 109 (VisitTree.leaf 108 [1, 1]) (VisitTree.leaf 109 [1, 1]))) (VisitTree.branch 448 (VisitTree.branch 447 (VisitTree.leaf 110 [1, 1]) (VisitTree.leaf 447 [1])) (VisitTree.branch 449 (VisitTree.leaf 448 [1]) (VisitTree.leaf 449 [1])))))) (VisitTree.branch 464 (VisitTree.branch 457 (VisitTree.branch 453 (VisitTree.branch 451 (VisitTree.leaf 450 [1]) (VisitTree.branch 452 (VisitTree.leaf 451 [1]) (VisitTree.leaf 452 [1]))) (VisitTree.branch 455 (VisitTree.branch 454 (VisitTree.leaf 453 [1]) (VisitTree.leaf 454 [1])) (VisitTree.branch 456 (VisitTree.leaf 455 [1]) (VisitTree.leaf 456 [1])))) (VisitTree.branch 460 (VisitTree.branch 458 (VisitTree.leaf 457 [1]) (VisitTree.branch 459 (VisitTree.leaf 458 [1]) (VisitTree.leaf 459 [1]))) (VisitTree.branch 462 (VisitTree.branch 461 (VisitTree.leaf 460 [1]) (VisitTree.leaf 461 [1])) (VisitTree.branch 463 (VisitTree.leaf 462 [1]) (VisitTree.leaf 463 [1]))))) (VisitTree.branch 471 (VisitTree.branch 467 (VisitTree.branch 465 (VisitTree.leaf 464 [1]) (VisitTree.branch 466 (VisitTree.leaf 465 [1]) (VisitTree.leaf 466 [1]))) (VisitTree.branch 469 (VisitTree.branch 468 (VisitTree.leaf 467 [1]) (VisitTree.leaf 468 [1])) (VisitTree.branch 470 (VisitTree.leaf 469 [1]) (VisitTree.leaf 470 [1])))) (VisitTree.branch 475 (VisitTree.branch 473 (VisitTree.branch 472 (VisitTree.leaf 471 [1]) (VisitTree.leaf 472 [1])) (VisitTree.branch 474 (VisitTree.leaf 473 [1]) (VisitTree.leaf 474 [1]))) (VisitTree.branch 477 (VisitTree.branch 476 (VisitTree.leaf 475 [1]) (VisitTree.leaf 476 [1])) (VisitTree.branch 478 (VisitTree.leaf 477 [1]) (VisitTree.leaf 478 [1])))))))

def fastForwardChunkVisits170 (r : Nat) : List Nat :=
  forwardVisitTree170.lookup r

private theorem covered170 :
    visitsCovered forwardEventChunk170 forwardVisitTree170 = true := by
  decide +kernel

private theorem checked170 :
    visitsChecked forwardEventChunk170 forwardVisitTree170 = true := by
  decide +kernel

theorem eventVisits_forwardChunk170 (r : Nat) :
    eventVisits r forwardEventChunk170 = fastForwardChunkVisits170 r :=
  eventVisits_of_tree _ _ covered170 checked170 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk170

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 171. -/
def forwardVisitTree171 : VisitTree := (VisitTree.branch 420 (VisitTree.branch 99 (VisitTree.branch 93 (VisitTree.branch 90 (VisitTree.branch 88 (VisitTree.leaf 87 [1]) (VisitTree.branch 89 (VisitTree.leaf 88 [1, 1]) (VisitTree.leaf 89 [1, 1]))) (VisitTree.branch 91 (VisitTree.leaf 90 [1, 1]) (VisitTree.branch 92 (VisitTree.leaf 91 [1, 1]) (VisitTree.leaf 92 [1, 1])))) (VisitTree.branch 96 (VisitTree.branch 94 (VisitTree.leaf 93 [1, 1]) (VisitTree.branch 95 (VisitTree.leaf 94 [1, 1]) (VisitTree.leaf 95 [1, 1]))) (VisitTree.branch 97 (VisitTree.leaf 96 [1, 1]) (VisitTree.branch 98 (VisitTree.leaf 97 [1, 1]) (VisitTree.leaf 98 [1, 1]))))) (VisitTree.branch 414 (VisitTree.branch 102 (VisitTree.branch 100 (VisitTree.leaf 99 [1, 1]) (VisitTree.branch 101 (VisitTree.leaf 100 [1, 1]) (VisitTree.leaf 101 [1, 1]))) (VisitTree.branch 103 (VisitTree.leaf 102 [1, 1]) (VisitTree.branch 413 (VisitTree.leaf 103 [1]) (VisitTree.leaf 413 [1])))) (VisitTree.branch 417 (VisitTree.branch 415 (VisitTree.leaf 414 [1]) (VisitTree.branch 416 (VisitTree.leaf 415 [1]) (VisitTree.leaf 416 [1]))) (VisitTree.branch 418 (VisitTree.leaf 417 [1]) (VisitTree.branch 419 (VisitTree.leaf 418 [1]) (VisitTree.leaf 419 [1])))))) (VisitTree.branch 432 (VisitTree.branch 426 (VisitTree.branch 423 (VisitTree.branch 421 (VisitTree.leaf 420 [1]) (VisitTree.branch 422 (VisitTree.leaf 421 [1]) (VisitTree.leaf 422 [1]))) (VisitTree.branch 424 (VisitTree.leaf 423 [1]) (VisitTree.branch 425 (VisitTree.leaf 424 [1]) (VisitTree.leaf 425 [1])))) (VisitTree.branch 429 (VisitTree.branch 427 (VisitTree.leaf 426 [1]) (VisitTree.branch 428 (VisitTree.leaf 427 [1]) (VisitTree.leaf 428 [1]))) (VisitTree.branch 430 (VisitTree.leaf 429 [1]) (VisitTree.branch 431 (VisitTree.leaf 430 [1]) (VisitTree.leaf 431 [1]))))) (VisitTree.branch 438 (VisitTree.branch 435 (VisitTree.branch 433 (VisitTree.leaf 432 [1]) (VisitTree.branch 434 (VisitTree.leaf 433 [1]) (VisitTree.leaf 434 [1]))) (VisitTree.branch 436 (VisitTree.leaf 435 [1]) (VisitTree.branch 437 (VisitTree.leaf 436 [1]) (VisitTree.leaf 437 [1])))) (VisitTree.branch 441 (VisitTree.branch 439 (VisitTree.leaf 438 [1]) (VisitTree.branch 440 (VisitTree.leaf 439 [1]) (VisitTree.leaf 440 [1]))) (VisitTree.branch 443 (VisitTree.branch 442 (VisitTree.leaf 441 [1]) (VisitTree.leaf 442 [1])) (VisitTree.branch 446 (VisitTree.leaf 443 [1]) (VisitTree.leaf 446 [1])))))))

def fastForwardChunkVisits171 (r : Nat) : List Nat :=
  forwardVisitTree171.lookup r

private theorem covered171 :
    visitsCovered forwardEventChunk171 forwardVisitTree171 = true := by
  decide +kernel

private theorem checked171 :
    visitsChecked forwardEventChunk171 forwardVisitTree171 = true := by
  decide +kernel

theorem eventVisits_forwardChunk171 (r : Nat) :
    eventVisits r forwardEventChunk171 = fastForwardChunkVisits171 r :=
  eventVisits_of_tree _ _ covered171 checked171 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk171

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 172. -/
def forwardVisitTree172 : VisitTree := (VisitTree.branch 386 (VisitTree.branch 83 (VisitTree.branch 77 (VisitTree.branch 74 (VisitTree.branch 72 (VisitTree.leaf 71 [1]) (VisitTree.branch 73 (VisitTree.leaf 72 [1, 1]) (VisitTree.leaf 73 [1, 1]))) (VisitTree.branch 75 (VisitTree.leaf 74 [1, 1]) (VisitTree.branch 76 (VisitTree.leaf 75 [1, 1]) (VisitTree.leaf 76 [1, 1])))) (VisitTree.branch 80 (VisitTree.branch 78 (VisitTree.leaf 77 [1, 1]) (VisitTree.branch 79 (VisitTree.leaf 78 [1, 1]) (VisitTree.leaf 79 [1, 1]))) (VisitTree.branch 81 (VisitTree.leaf 80 [1, 1]) (VisitTree.branch 82 (VisitTree.leaf 81 [1, 1]) (VisitTree.leaf 82 [1, 1]))))) (VisitTree.branch 380 (VisitTree.branch 86 (VisitTree.branch 84 (VisitTree.leaf 83 [1, 1]) (VisitTree.branch 85 (VisitTree.leaf 84 [1, 1]) (VisitTree.leaf 85 [1, 1]))) (VisitTree.branch 87 (VisitTree.leaf 86 [1, 1]) (VisitTree.branch 379 (VisitTree.leaf 87 [1]) (VisitTree.leaf 379 [1])))) (VisitTree.branch 383 (VisitTree.branch 381 (VisitTree.leaf 380 [1]) (VisitTree.branch 382 (VisitTree.leaf 381 [1]) (VisitTree.leaf 382 [1]))) (VisitTree.branch 384 (VisitTree.leaf 383 [1]) (VisitTree.branch 385 (VisitTree.leaf 384 [1]) (VisitTree.leaf 385 [1])))))) (VisitTree.branch 398 (VisitTree.branch 392 (VisitTree.branch 389 (VisitTree.branch 387 (VisitTree.leaf 386 [1]) (VisitTree.branch 388 (VisitTree.leaf 387 [1]) (VisitTree.leaf 388 [1]))) (VisitTree.branch 390 (VisitTree.leaf 389 [1]) (VisitTree.branch 391 (VisitTree.leaf 390 [1]) (VisitTree.leaf 391 [1])))) (VisitTree.branch 395 (VisitTree.branch 393 (VisitTree.leaf 392 [1]) (VisitTree.branch 394 (VisitTree.leaf 393 [1]) (VisitTree.leaf 394 [1]))) (VisitTree.branch 396 (VisitTree.leaf 395 [1]) (VisitTree.branch 397 (VisitTree.leaf 396 [1]) (VisitTree.leaf 397 [1]))))) (VisitTree.branch 406 (VisitTree.branch 403 (VisitTree.branch 399 (VisitTree.leaf 398 [1]) (VisitTree.branch 402 (VisitTree.leaf 399 [1]) (VisitTree.leaf 402 [1]))) (VisitTree.branch 404 (VisitTree.leaf 403 [1]) (VisitTree.branch 405 (VisitTree.leaf 404 [1]) (VisitTree.leaf 405 [1])))) (VisitTree.branch 409 (VisitTree.branch 407 (VisitTree.leaf 406 [1]) (VisitTree.branch 408 (VisitTree.leaf 407 [1]) (VisitTree.leaf 408 [1]))) (VisitTree.branch 411 (VisitTree.branch 410 (VisitTree.leaf 409 [1]) (VisitTree.leaf 410 [1])) (VisitTree.branch 412 (VisitTree.leaf 411 [1]) (VisitTree.leaf 412 [1])))))))

def fastForwardChunkVisits172 (r : Nat) : List Nat :=
  forwardVisitTree172.lookup r

private theorem covered172 :
    visitsCovered forwardEventChunk172 forwardVisitTree172 = true := by
  decide +kernel

private theorem checked172 :
    visitsChecked forwardEventChunk172 forwardVisitTree172 = true := by
  decide +kernel

theorem eventVisits_forwardChunk172 (r : Nat) :
    eventVisits r forwardEventChunk172 = fastForwardChunkVisits172 r :=
  eventVisits_of_tree _ _ covered172 checked172 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk172

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 173. -/
def forwardVisitTree173 : VisitTree := (VisitTree.branch 350 (VisitTree.branch 67 (VisitTree.branch 61 (VisitTree.branch 58 (VisitTree.branch 56 (VisitTree.leaf 55 [1]) (VisitTree.branch 57 (VisitTree.leaf 56 [1, 1]) (VisitTree.leaf 57 [1, 1]))) (VisitTree.branch 59 (VisitTree.leaf 58 [1, 1]) (VisitTree.branch 60 (VisitTree.leaf 59 [1, 1]) (VisitTree.leaf 60 [1, 1])))) (VisitTree.branch 64 (VisitTree.branch 62 (VisitTree.leaf 61 [1, 1]) (VisitTree.branch 63 (VisitTree.leaf 62 [1, 1]) (VisitTree.leaf 63 [1, 1]))) (VisitTree.branch 65 (VisitTree.leaf 64 [1, 1]) (VisitTree.branch 66 (VisitTree.leaf 65 [1, 1]) (VisitTree.leaf 66 [1, 1]))))) (VisitTree.branch 344 (VisitTree.branch 70 (VisitTree.branch 68 (VisitTree.leaf 67 [1, 1]) (VisitTree.branch 69 (VisitTree.leaf 68 [1, 1]) (VisitTree.leaf 69 [1, 1]))) (VisitTree.branch 71 (VisitTree.leaf 70 [1, 1]) (VisitTree.branch 343 (VisitTree.leaf 71 [1]) (VisitTree.leaf 343 [1])))) (VisitTree.branch 347 (VisitTree.branch 345 (VisitTree.leaf 344 [1]) (VisitTree.branch 346 (VisitTree.leaf 345 [1]) (VisitTree.leaf 346 [1]))) (VisitTree.branch 348 (VisitTree.leaf 347 [1]) (VisitTree.branch 349 (VisitTree.leaf 348 [1]) (VisitTree.leaf 349 [1])))))) (VisitTree.branch 364 (VisitTree.branch 358 (VisitTree.branch 353 (VisitTree.branch 351 (VisitTree.leaf 350 [1]) (VisitTree.branch 352 (VisitTree.leaf 351 [1]) (VisitTree.leaf 352 [1]))) (VisitTree.branch 356 (VisitTree.leaf 353 [1]) (VisitTree.branch 357 (VisitTree.leaf 356 [1]) (VisitTree.leaf 357 [1])))) (VisitTree.branch 361 (VisitTree.branch 359 (VisitTree.leaf 358 [1]) (VisitTree.branch 360 (VisitTree.leaf 359 [1]) (VisitTree.leaf 360 [1]))) (VisitTree.branch 362 (VisitTree.leaf 361 [1]) (VisitTree.branch 363 (VisitTree.leaf 362 [1]) (VisitTree.leaf 363 [1]))))) (VisitTree.branch 372 (VisitTree.branch 369 (VisitTree.branch 365 (VisitTree.leaf 364 [1]) (VisitTree.branch 368 (VisitTree.leaf 365 [1]) (VisitTree.leaf 368 [1]))) (VisitTree.branch 370 (VisitTree.leaf 369 [1]) (VisitTree.branch 371 (VisitTree.leaf 370 [1]) (VisitTree.leaf 371 [1])))) (VisitTree.branch 375 (VisitTree.branch 373 (VisitTree.leaf 372 [1]) (VisitTree.branch 374 (VisitTree.leaf 373 [1]) (VisitTree.leaf 374 [1]))) (VisitTree.branch 377 (VisitTree.branch 376 (VisitTree.leaf 375 [1]) (VisitTree.leaf 376 [1])) (VisitTree.branch 378 (VisitTree.leaf 377 [1]) (VisitTree.leaf 378 [1])))))))

def fastForwardChunkVisits173 (r : Nat) : List Nat :=
  forwardVisitTree173.lookup r

private theorem covered173 :
    visitsCovered forwardEventChunk173 forwardVisitTree173 = true := by
  decide +kernel

private theorem checked173 :
    visitsChecked forwardEventChunk173 forwardVisitTree173 = true := by
  decide +kernel

theorem eventVisits_forwardChunk173 (r : Nat) :
    eventVisits r forwardEventChunk173 = fastForwardChunkVisits173 r :=
  eventVisits_of_tree _ _ covered173 checked173 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk173

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 174. -/
def forwardVisitTree174 : VisitTree := (VisitTree.branch 312 (VisitTree.branch 51 (VisitTree.branch 45 (VisitTree.branch 42 (VisitTree.branch 40 (VisitTree.leaf 39 [1]) (VisitTree.branch 41 (VisitTree.leaf 40 [1, 1]) (VisitTree.leaf 41 [1, 1]))) (VisitTree.branch 43 (VisitTree.leaf 42 [1, 1]) (VisitTree.branch 44 (VisitTree.leaf 43 [1, 1]) (VisitTree.leaf 44 [1, 1])))) (VisitTree.branch 48 (VisitTree.branch 46 (VisitTree.leaf 45 [1, 1]) (VisitTree.branch 47 (VisitTree.leaf 46 [1, 1]) (VisitTree.leaf 47 [1, 1]))) (VisitTree.branch 49 (VisitTree.leaf 48 [1, 1]) (VisitTree.branch 50 (VisitTree.leaf 49 [1, 1]) (VisitTree.leaf 50 [1, 1]))))) (VisitTree.branch 306 (VisitTree.branch 54 (VisitTree.branch 52 (VisitTree.leaf 51 [1, 1]) (VisitTree.branch 53 (VisitTree.leaf 52 [1, 1]) (VisitTree.leaf 53 [1, 1]))) (VisitTree.branch 55 (VisitTree.leaf 54 [1, 1]) (VisitTree.branch 305 (VisitTree.leaf 55 [1]) (VisitTree.leaf 305 [1])))) (VisitTree.branch 309 (VisitTree.branch 307 (VisitTree.leaf 306 [1]) (VisitTree.branch 308 (VisitTree.leaf 307 [1]) (VisitTree.leaf 308 [1]))) (VisitTree.branch 310 (VisitTree.leaf 309 [1]) (VisitTree.branch 311 (VisitTree.leaf 310 [1]) (VisitTree.leaf 311 [1])))))) (VisitTree.branch 326 (VisitTree.branch 318 (VisitTree.branch 315 (VisitTree.branch 313 (VisitTree.leaf 312 [1]) (VisitTree.branch 314 (VisitTree.leaf 313 [1]) (VisitTree.leaf 314 [1]))) (VisitTree.branch 316 (VisitTree.leaf 315 [1]) (VisitTree.branch 317 (VisitTree.leaf 316 [1]) (VisitTree.leaf 317 [1])))) (VisitTree.branch 321 (VisitTree.branch 319 (VisitTree.leaf 318 [1]) (VisitTree.branch 320 (VisitTree.leaf 319 [1]) (VisitTree.leaf 320 [1]))) (VisitTree.branch 322 (VisitTree.leaf 321 [1]) (VisitTree.branch 323 (VisitTree.leaf 322 [1]) (VisitTree.leaf 323 [1]))))) (VisitTree.branch 336 (VisitTree.branch 331 (VisitTree.branch 327 (VisitTree.leaf 326 [1]) (VisitTree.branch 330 (VisitTree.leaf 327 [1]) (VisitTree.leaf 330 [1]))) (VisitTree.branch 332 (VisitTree.leaf 331 [1]) (VisitTree.branch 333 (VisitTree.leaf 332 [1]) (VisitTree.leaf 333 [1])))) (VisitTree.branch 339 (VisitTree.branch 337 (VisitTree.leaf 336 [1]) (VisitTree.branch 338 (VisitTree.leaf 337 [1]) (VisitTree.leaf 338 [1]))) (VisitTree.branch 341 (VisitTree.branch 340 (VisitTree.leaf 339 [1]) (VisitTree.leaf 340 [1])) (VisitTree.branch 342 (VisitTree.leaf 341 [1]) (VisitTree.leaf 342 [1])))))))

def fastForwardChunkVisits174 (r : Nat) : List Nat :=
  forwardVisitTree174.lookup r

private theorem covered174 :
    visitsCovered forwardEventChunk174 forwardVisitTree174 = true := by
  decide +kernel

private theorem checked174 :
    visitsChecked forwardEventChunk174 forwardVisitTree174 = true := by
  decide +kernel

theorem eventVisits_forwardChunk174 (r : Nat) :
    eventVisits r forwardEventChunk174 = fastForwardChunkVisits174 r :=
  eventVisits_of_tree _ _ covered174 checked174 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk174

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 175. -/
def forwardVisitTree175 : VisitTree := (VisitTree.branch 280 (VisitTree.branch 35 (VisitTree.branch 29 (VisitTree.branch 26 (VisitTree.branch 24 (VisitTree.leaf 23 [1]) (VisitTree.branch 25 (VisitTree.leaf 24 [1, 1]) (VisitTree.leaf 25 [1, 1]))) (VisitTree.branch 27 (VisitTree.leaf 26 [1, 1]) (VisitTree.branch 28 (VisitTree.leaf 27 [1, 1]) (VisitTree.leaf 28 [1, 1])))) (VisitTree.branch 32 (VisitTree.branch 30 (VisitTree.leaf 29 [1, 1]) (VisitTree.branch 31 (VisitTree.leaf 30 [1, 1]) (VisitTree.leaf 31 [1, 1]))) (VisitTree.branch 33 (VisitTree.leaf 32 [1, 1]) (VisitTree.branch 34 (VisitTree.leaf 33 [1, 1]) (VisitTree.leaf 34 [1, 1]))))) (VisitTree.branch 274 (VisitTree.branch 38 (VisitTree.branch 36 (VisitTree.leaf 35 [1, 1]) (VisitTree.branch 37 (VisitTree.leaf 36 [1, 1]) (VisitTree.leaf 37 [1, 1]))) (VisitTree.branch 39 (VisitTree.leaf 38 [1, 1]) (VisitTree.branch 273 (VisitTree.leaf 39 [1]) (VisitTree.leaf 273 [1])))) (VisitTree.branch 277 (VisitTree.branch 275 (VisitTree.leaf 274 [1]) (VisitTree.branch 276 (VisitTree.leaf 275 [1]) (VisitTree.leaf 276 [1]))) (VisitTree.branch 278 (VisitTree.leaf 277 [1]) (VisitTree.branch 279 (VisitTree.leaf 278 [1]) (VisitTree.leaf 279 [1])))))) (VisitTree.branch 292 (VisitTree.branch 286 (VisitTree.branch 283 (VisitTree.branch 281 (VisitTree.leaf 280 [1]) (VisitTree.branch 282 (VisitTree.leaf 281 [1]) (VisitTree.leaf 282 [1]))) (VisitTree.branch 284 (VisitTree.leaf 283 [1]) (VisitTree.branch 285 (VisitTree.leaf 284 [1]) (VisitTree.leaf 285 [1])))) (VisitTree.branch 289 (VisitTree.branch 287 (VisitTree.leaf 286 [1]) (VisitTree.branch 288 (VisitTree.leaf 287 [1]) (VisitTree.leaf 288 [1]))) (VisitTree.branch 290 (VisitTree.leaf 289 [1]) (VisitTree.branch 291 (VisitTree.leaf 290 [1]) (VisitTree.leaf 291 [1]))))) (VisitTree.branch 298 (VisitTree.branch 295 (VisitTree.branch 293 (VisitTree.leaf 292 [1]) (VisitTree.branch 294 (VisitTree.leaf 293 [1]) (VisitTree.leaf 294 [1]))) (VisitTree.branch 296 (VisitTree.leaf 295 [1]) (VisitTree.branch 297 (VisitTree.leaf 296 [1]) (VisitTree.leaf 297 [1])))) (VisitTree.branch 301 (VisitTree.branch 299 (VisitTree.leaf 298 [1]) (VisitTree.branch 300 (VisitTree.leaf 299 [1]) (VisitTree.leaf 300 [1]))) (VisitTree.branch 303 (VisitTree.branch 302 (VisitTree.leaf 301 [1]) (VisitTree.leaf 302 [1])) (VisitTree.branch 304 (VisitTree.leaf 303 [1]) (VisitTree.leaf 304 [1])))))))

def fastForwardChunkVisits175 (r : Nat) : List Nat :=
  forwardVisitTree175.lookup r

private theorem covered175 :
    visitsCovered forwardEventChunk175 forwardVisitTree175 = true := by
  decide +kernel

private theorem checked175 :
    visitsChecked forwardEventChunk175 forwardVisitTree175 = true := by
  decide +kernel

theorem eventVisits_forwardChunk175 (r : Nat) :
    eventVisits r forwardEventChunk175 = fastForwardChunkVisits175 r :=
  eventVisits_of_tree _ _ covered175 checked175 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk175

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 176. -/
def forwardVisitTree176 : VisitTree := (VisitTree.branch 246 (VisitTree.branch 19 (VisitTree.branch 13 (VisitTree.branch 10 (VisitTree.branch 8 (VisitTree.leaf 7 [1]) (VisitTree.branch 9 (VisitTree.leaf 8 [1, 1]) (VisitTree.leaf 9 [1, 1]))) (VisitTree.branch 11 (VisitTree.leaf 10 [1, 1]) (VisitTree.branch 12 (VisitTree.leaf 11 [1, 1]) (VisitTree.leaf 12 [1, 1])))) (VisitTree.branch 16 (VisitTree.branch 14 (VisitTree.leaf 13 [1, 1]) (VisitTree.branch 15 (VisitTree.leaf 14 [1, 1]) (VisitTree.leaf 15 [1, 1]))) (VisitTree.branch 17 (VisitTree.leaf 16 [1, 1]) (VisitTree.branch 18 (VisitTree.leaf 17 [1, 1]) (VisitTree.leaf 18 [1, 1]))))) (VisitTree.branch 238 (VisitTree.branch 22 (VisitTree.branch 20 (VisitTree.leaf 19 [1, 1]) (VisitTree.branch 21 (VisitTree.leaf 20 [1, 1]) (VisitTree.leaf 21 [1, 1]))) (VisitTree.branch 23 (VisitTree.leaf 22 [1, 1]) (VisitTree.branch 237 (VisitTree.leaf 23 [1]) (VisitTree.leaf 237 [1])))) (VisitTree.branch 241 (VisitTree.branch 239 (VisitTree.leaf 238 [1]) (VisitTree.branch 240 (VisitTree.leaf 239 [1]) (VisitTree.leaf 240 [1]))) (VisitTree.branch 244 (VisitTree.leaf 241 [1]) (VisitTree.branch 245 (VisitTree.leaf 244 [1]) (VisitTree.leaf 245 [1])))))) (VisitTree.branch 260 (VisitTree.branch 254 (VisitTree.branch 249 (VisitTree.branch 247 (VisitTree.leaf 246 [1]) (VisitTree.branch 248 (VisitTree.leaf 247 [1]) (VisitTree.leaf 248 [1]))) (VisitTree.branch 250 (VisitTree.leaf 249 [1]) (VisitTree.branch 251 (VisitTree.leaf 250 [1]) (VisitTree.leaf 251 [1])))) (VisitTree.branch 257 (VisitTree.branch 255 (VisitTree.leaf 254 [1]) (VisitTree.branch 256 (VisitTree.leaf 255 [1]) (VisitTree.leaf 256 [1]))) (VisitTree.branch 258 (VisitTree.leaf 257 [1]) (VisitTree.branch 259 (VisitTree.leaf 258 [1]) (VisitTree.leaf 259 [1]))))) (VisitTree.branch 266 (VisitTree.branch 263 (VisitTree.branch 261 (VisitTree.leaf 260 [1]) (VisitTree.branch 262 (VisitTree.leaf 261 [1]) (VisitTree.leaf 262 [1]))) (VisitTree.branch 264 (VisitTree.leaf 263 [1]) (VisitTree.branch 265 (VisitTree.leaf 264 [1]) (VisitTree.leaf 265 [1])))) (VisitTree.branch 269 (VisitTree.branch 267 (VisitTree.leaf 266 [1]) (VisitTree.branch 268 (VisitTree.leaf 267 [1]) (VisitTree.leaf 268 [1]))) (VisitTree.branch 271 (VisitTree.branch 270 (VisitTree.leaf 269 [1]) (VisitTree.leaf 270 [1])) (VisitTree.branch 272 (VisitTree.leaf 271 [1]) (VisitTree.leaf 272 [1])))))))

def fastForwardChunkVisits176 (r : Nat) : List Nat :=
  forwardVisitTree176.lookup r

private theorem covered176 :
    visitsCovered forwardEventChunk176 forwardVisitTree176 = true := by
  decide +kernel

private theorem checked176 :
    visitsChecked forwardEventChunk176 forwardVisitTree176 = true := by
  decide +kernel

theorem eventVisits_forwardChunk176 (r : Nat) :
    eventVisits r forwardEventChunk176 = fastForwardChunkVisits176 r :=
  eventVisits_of_tree _ _ covered176 checked176 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk176

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 177. -/
def forwardVisitTree177 : VisitTree := (VisitTree.branch 225 (VisitTree.branch 5 (VisitTree.branch 2 (VisitTree.branch 1 (VisitTree.leaf 0 [1, 1]) (VisitTree.leaf 1 [1, 1])) (VisitTree.branch 3 (VisitTree.leaf 2 [1, 1]) (VisitTree.branch 4 (VisitTree.leaf 3 [1, 1]) (VisitTree.leaf 4 [1, 1])))) (VisitTree.branch 222 (VisitTree.branch 6 (VisitTree.leaf 5 [1, 1]) (VisitTree.branch 7 (VisitTree.leaf 6 [1, 1]) (VisitTree.leaf 7 [1]))) (VisitTree.branch 223 (VisitTree.leaf 222 [1]) (VisitTree.branch 224 (VisitTree.leaf 223 [1]) (VisitTree.leaf 224 [1]))))) (VisitTree.branch 231 (VisitTree.branch 228 (VisitTree.branch 226 (VisitTree.leaf 225 [1]) (VisitTree.branch 227 (VisitTree.leaf 226 [1]) (VisitTree.leaf 227 [1]))) (VisitTree.branch 229 (VisitTree.leaf 228 [1]) (VisitTree.branch 230 (VisitTree.leaf 229 [1]) (VisitTree.leaf 230 [1])))) (VisitTree.branch 234 (VisitTree.branch 232 (VisitTree.leaf 231 [1]) (VisitTree.branch 233 (VisitTree.leaf 232 [1]) (VisitTree.leaf 233 [1]))) (VisitTree.branch 235 (VisitTree.leaf 234 [1]) (VisitTree.branch 236 (VisitTree.leaf 235 [1]) (VisitTree.leaf 236 [1]))))))

def fastForwardChunkVisits177 (r : Nat) : List Nat :=
  forwardVisitTree177.lookup r

private theorem covered177 :
    visitsCovered forwardEventChunk177 forwardVisitTree177 = true := by
  decide +kernel

private theorem checked177 :
    visitsChecked forwardEventChunk177 forwardVisitTree177 = true := by
  decide +kernel

theorem eventVisits_forwardChunk177 (r : Nat) :
    eventVisits r forwardEventChunk177 = fastForwardChunkVisits177 r :=
  eventVisits_of_tree _ _ covered177 checked177 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk177


