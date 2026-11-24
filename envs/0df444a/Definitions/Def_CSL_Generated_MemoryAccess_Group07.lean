-- Prove2me | Definitions.Def_CSL_Generated_MemoryAccess_Group07
-- name    : CSL_Generated_MemoryAccess_Group07
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T13:32:03.279806+00:00
-- url     : https://prove2.me/theorems/fb04d111-1c5d-41c3-b936-675f43c2c979
-- title:
--   Coded sorting library: Generated / MemoryAccess / Group07
-- statement:
--   Module `CodedSorting.Generated.MemoryAccess.Group07` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Generated.MemoryAccess.Group07

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Circuit_MemoryAccess_PhysicalFrameEventChunkData
import Definitions.Def_CSL_Generated_MemoryAccess_Base

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 116. -/
def forwardVisitTree116 : VisitTree := (VisitTree.branch 568 (VisitTree.branch 314 (VisitTree.branch 263 (VisitTree.branch 236 (VisitTree.branch 230 (VisitTree.branch 226 (VisitTree.leaf 224 [1]) (VisitTree.leaf 226 [1])) (VisitTree.branch 231 (VisitTree.leaf 230 [1]) (VisitTree.leaf 231 [1]))) (VisitTree.branch 260 (VisitTree.branch 255 (VisitTree.leaf 236 [1]) (VisitTree.leaf 255 [1])) (VisitTree.branch 262 (VisitTree.leaf 260 [1]) (VisitTree.leaf 262 [1])))) (VisitTree.branch 276 (VisitTree.branch 267 (VisitTree.branch 266 (VisitTree.leaf 263 [1]) (VisitTree.leaf 266 [1])) (VisitTree.branch 275 (VisitTree.leaf 267 [1]) (VisitTree.leaf 275 [1]))) (VisitTree.branch 300 (VisitTree.branch 283 (VisitTree.leaf 276 [1]) (VisitTree.leaf 283 [1])) (VisitTree.branch 306 (VisitTree.leaf 300 [1]) (VisitTree.leaf 306 [1]))))) (VisitTree.branch 429 (VisitTree.branch 419 (VisitTree.branch 406 (VisitTree.branch 330 (VisitTree.leaf 314 [1]) (VisitTree.leaf 330 [1])) (VisitTree.branch 418 (VisitTree.leaf 406 [1]) (VisitTree.leaf 418 [1]))) (VisitTree.branch 424 (VisitTree.branch 423 (VisitTree.leaf 419 [1]) (VisitTree.leaf 423 [1])) (VisitTree.branch 425 (VisitTree.leaf 424 [1]) (VisitTree.leaf 425 [1])))) (VisitTree.branch 441 (VisitTree.branch 438 (VisitTree.branch 434 (VisitTree.leaf 429 [1]) (VisitTree.leaf 434 [1])) (VisitTree.branch 439 (VisitTree.leaf 438 [1]) (VisitTree.leaf 439 [1]))) (VisitTree.branch 447 (VisitTree.branch 446 (VisitTree.leaf 441 [1]) (VisitTree.leaf 446 [1])) (VisitTree.branch 458 (VisitTree.leaf 447 [1]) (VisitTree.leaf 458 [1])))))) (VisitTree.branch 629 (VisitTree.branch 608 (VisitTree.branch 590 (VisitTree.branch 577 (VisitTree.branch 575 (VisitTree.leaf 568 [1]) (VisitTree.leaf 575 [1])) (VisitTree.branch 586 (VisitTree.leaf 577 [1]) (VisitTree.leaf 586 [1]))) (VisitTree.branch 592 (VisitTree.branch 591 (VisitTree.leaf 590 [1]) (VisitTree.leaf 591 [1])) (VisitTree.branch 593 (VisitTree.leaf 592 [1]) (VisitTree.leaf 593 [1])))) (VisitTree.branch 616 (VisitTree.branch 611 (VisitTree.branch 609 (VisitTree.leaf 608 [1]) (VisitTree.leaf 609 [1])) (VisitTree.branch 615 (VisitTree.leaf 611 [1]) (VisitTree.leaf 615 [1]))) (VisitTree.branch 622 (VisitTree.branch 620 (VisitTree.leaf 616 [1]) (VisitTree.leaf 620 [1])) (VisitTree.branch 625 (VisitTree.leaf 622 [1]) (VisitTree.leaf 625 [1]))))) (VisitTree.branch 638 (VisitTree.branch 633 (VisitTree.branch 631 (VisitTree.branch 630 (VisitTree.leaf 629 [1]) (VisitTree.leaf 630 [1])) (VisitTree.branch 632 (VisitTree.leaf 631 [1]) (VisitTree.leaf 632 [1]))) (VisitTree.branch 635 (VisitTree.branch 634 (VisitTree.leaf 633 [1]) (VisitTree.leaf 634 [1])) (VisitTree.branch 636 (VisitTree.leaf 635 [1]) (VisitTree.leaf 636 [1])))) (VisitTree.branch 642 (VisitTree.branch 640 (VisitTree.branch 639 (VisitTree.leaf 638 [1]) (VisitTree.leaf 639 [1])) (VisitTree.branch 641 (VisitTree.leaf 640 [1]) (VisitTree.leaf 641 [1]))) (VisitTree.branch 655 (VisitTree.branch 653 (VisitTree.leaf 642 [1]) (VisitTree.leaf 653 [1])) (VisitTree.branch 660 (VisitTree.leaf 655 [1]) (VisitTree.leaf 660 [1])))))))

def fastForwardChunkVisits116 (r : Nat) : List Nat :=
  forwardVisitTree116.lookup r

private theorem covered116 :
    visitsCovered forwardEventChunk116 forwardVisitTree116 = true := by
  decide +kernel

private theorem checked116 :
    visitsChecked forwardEventChunk116 forwardVisitTree116 = true := by
  decide +kernel

theorem eventVisits_forwardChunk116 (r : Nat) :
    eventVisits r forwardEventChunk116 = fastForwardChunkVisits116 r :=
  eventVisits_of_tree _ _ covered116 checked116 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk116

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 117. -/
def forwardVisitTree117 : VisitTree := (VisitTree.branch 527 (VisitTree.branch 370 (VisitTree.branch 328 (VisitTree.branch 302 (VisitTree.branch 292 (VisitTree.branch 249 (VisitTree.leaf 244 [1]) (VisitTree.leaf 249 [1])) (VisitTree.branch 294 (VisitTree.leaf 292 [1]) (VisitTree.leaf 294 [1]))) (VisitTree.branch 304 (VisitTree.branch 303 (VisitTree.leaf 302 [1]) (VisitTree.leaf 303 [1])) (VisitTree.branch 318 (VisitTree.leaf 304 [1]) (VisitTree.leaf 318 [1])))) (VisitTree.branch 339 (VisitTree.branch 334 (VisitTree.branch 331 (VisitTree.leaf 328 [1]) (VisitTree.leaf 331 [1])) (VisitTree.branch 335 (VisitTree.leaf 334 [1]) (VisitTree.leaf 335 [1]))) (VisitTree.branch 353 (VisitTree.branch 350 (VisitTree.leaf 339 [1]) (VisitTree.leaf 350 [1])) (VisitTree.branch 367 (VisitTree.leaf 353 [1]) (VisitTree.leaf 367 [1]))))) (VisitTree.branch 412 (VisitTree.branch 390 (VisitTree.branch 376 (VisitTree.branch 374 (VisitTree.leaf 370 [1]) (VisitTree.leaf 374 [1])) (VisitTree.branch 383 (VisitTree.leaf 376 [1]) (VisitTree.leaf 383 [1]))) (VisitTree.branch 392 (VisitTree.branch 391 (VisitTree.leaf 390 [1]) (VisitTree.leaf 391 [1])) (VisitTree.branch 397 (VisitTree.leaf 392 [1]) (VisitTree.leaf 397 [1])))) (VisitTree.branch 454 (VisitTree.branch 445 (VisitTree.branch 422 (VisitTree.leaf 412 [1]) (VisitTree.leaf 422 [1])) (VisitTree.branch 453 (VisitTree.leaf 445 [1]) (VisitTree.leaf 453 [1]))) (VisitTree.branch 481 (VisitTree.branch 457 (VisitTree.leaf 454 [1]) (VisitTree.leaf 457 [1])) (VisitTree.branch 513 (VisitTree.leaf 481 [1]) (VisitTree.leaf 513 [1])))))) (VisitTree.branch 583 (VisitTree.branch 565 (VisitTree.branch 547 (VisitTree.branch 542 (VisitTree.branch 529 (VisitTree.leaf 527 [1]) (VisitTree.leaf 529 [1])) (VisitTree.branch 545 (VisitTree.leaf 542 [1]) (VisitTree.leaf 545 [1]))) (VisitTree.branch 558 (VisitTree.branch 552 (VisitTree.leaf 547 [1]) (VisitTree.leaf 552 [1])) (VisitTree.branch 560 (VisitTree.leaf 558 [1]) (VisitTree.leaf 560 [1])))) (VisitTree.branch 578 (VisitTree.branch 572 (VisitTree.branch 571 (VisitTree.leaf 565 [1]) (VisitTree.leaf 571 [1])) (VisitTree.branch 576 (VisitTree.leaf 572 [1]) (VisitTree.leaf 576 [1]))) (VisitTree.branch 580 (VisitTree.branch 579 (VisitTree.leaf 578 [1]) (VisitTree.leaf 579 [1])) (VisitTree.branch 581 (VisitTree.leaf 580 [1]) (VisitTree.leaf 581 [1]))))) (VisitTree.branch 613 (VisitTree.branch 589 (VisitTree.branch 587 (VisitTree.branch 585 (VisitTree.leaf 583 [1]) (VisitTree.leaf 585 [1])) (VisitTree.branch 588 (VisitTree.leaf 587 [1]) (VisitTree.leaf 588 [1]))) (VisitTree.branch 603 (VisitTree.branch 594 (VisitTree.leaf 589 [1]) (VisitTree.leaf 594 [1])) (VisitTree.branch 604 (VisitTree.leaf 603 [1]) (VisitTree.leaf 604 [1])))) (VisitTree.branch 621 (VisitTree.branch 618 (VisitTree.branch 614 (VisitTree.leaf 613 [1]) (VisitTree.leaf 614 [1])) (VisitTree.branch 619 (VisitTree.leaf 618 [1]) (VisitTree.leaf 619 [1]))) (VisitTree.branch 626 (VisitTree.branch 624 (VisitTree.leaf 621 [1]) (VisitTree.leaf 624 [1])) (VisitTree.branch 627 (VisitTree.leaf 626 [1]) (VisitTree.leaf 627 [1])))))))

def fastForwardChunkVisits117 (r : Nat) : List Nat :=
  forwardVisitTree117.lookup r

private theorem covered117 :
    visitsCovered forwardEventChunk117 forwardVisitTree117 = true := by
  decide +kernel

private theorem checked117 :
    visitsChecked forwardEventChunk117 forwardVisitTree117 = true := by
  decide +kernel

theorem eventVisits_forwardChunk117 (r : Nat) :
    eventVisits r forwardEventChunk117 = fastForwardChunkVisits117 r :=
  eventVisits_of_tree _ _ covered117 checked117 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk117

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 118. -/
def forwardVisitTree118 : VisitTree := (VisitTree.branch 519 (VisitTree.branch 362 (VisitTree.branch 296 (VisitTree.branch 270 (VisitTree.branch 268 (VisitTree.branch 261 (VisitTree.leaf 225 [1]) (VisitTree.leaf 261 [1])) (VisitTree.branch 269 (VisitTree.leaf 268 [1]) (VisitTree.leaf 269 [1]))) (VisitTree.branch 280 (VisitTree.branch 279 (VisitTree.leaf 270 [1]) (VisitTree.leaf 279 [1])) (VisitTree.branch 285 (VisitTree.leaf 280 [1]) (VisitTree.leaf 285 [1])))) (VisitTree.branch 337 (VisitTree.branch 299 (VisitTree.branch 298 (VisitTree.leaf 296 [1]) (VisitTree.leaf 298 [1])) (VisitTree.branch 315 (VisitTree.leaf 299 [1]) (VisitTree.leaf 315 [1]))) (VisitTree.branch 343 (VisitTree.branch 342 (VisitTree.leaf 337 [1]) (VisitTree.leaf 342 [1])) (VisitTree.branch 346 (VisitTree.leaf 343 [1]) (VisitTree.leaf 346 [1]))))) (VisitTree.branch 427 (VisitTree.branch 388 (VisitTree.branch 378 (VisitTree.branch 369 (VisitTree.leaf 362 [1]) (VisitTree.leaf 369 [1])) (VisitTree.branch 379 (VisitTree.leaf 378 [1]) (VisitTree.leaf 379 [1]))) (VisitTree.branch 395 (VisitTree.branch 389 (VisitTree.leaf 388 [1]) (VisitTree.leaf 389 [1])) (VisitTree.branch 401 (VisitTree.leaf 395 [1]) (VisitTree.leaf 401 [1])))) (VisitTree.branch 442 (VisitTree.branch 437 (VisitTree.branch 431 (VisitTree.leaf 427 [1]) (VisitTree.leaf 431 [1])) (VisitTree.branch 440 (VisitTree.leaf 437 [1]) (VisitTree.leaf 440 [1]))) (VisitTree.branch 487 (VisitTree.branch 448 (VisitTree.leaf 442 [1]) (VisitTree.leaf 448 [1])) (VisitTree.branch 492 (VisitTree.leaf 487 [1]) (VisitTree.leaf 492 [1])))))) (VisitTree.branch 562 (VisitTree.branch 540 (VisitTree.branch 528 (VisitTree.branch 523 (VisitTree.branch 522 (VisitTree.leaf 519 [1]) (VisitTree.leaf 522 [1])) (VisitTree.branch 524 (VisitTree.leaf 523 [1]) (VisitTree.leaf 524 [1]))) (VisitTree.branch 537 (VisitTree.branch 531 (VisitTree.leaf 528 [1]) (VisitTree.leaf 531 [1])) (VisitTree.branch 538 (VisitTree.leaf 537 [1]) (VisitTree.leaf 538 [1])))) (VisitTree.branch 554 (VisitTree.branch 551 (VisitTree.branch 544 (VisitTree.leaf 540 [1]) (VisitTree.leaf 544 [1])) (VisitTree.branch 553 (VisitTree.leaf 551 [1]) (VisitTree.leaf 553 [1]))) (VisitTree.branch 557 (VisitTree.branch 556 (VisitTree.leaf 554 [1]) (VisitTree.leaf 556 [1])) (VisitTree.branch 559 (VisitTree.leaf 557 [1]) (VisitTree.leaf 559 [1]))))) (VisitTree.branch 597 (VisitTree.branch 567 (VisitTree.branch 564 (VisitTree.branch 563 (VisitTree.leaf 562 [1]) (VisitTree.leaf 563 [1])) (VisitTree.branch 566 (VisitTree.leaf 564 [1]) (VisitTree.leaf 566 [1]))) (VisitTree.branch 584 (VisitTree.branch 582 (VisitTree.leaf 567 [1]) (VisitTree.leaf 582 [1])) (VisitTree.branch 596 (VisitTree.leaf 584 [1]) (VisitTree.leaf 596 [1])))) (VisitTree.branch 605 (VisitTree.branch 599 (VisitTree.branch 598 (VisitTree.leaf 597 [1]) (VisitTree.leaf 598 [1])) (VisitTree.branch 602 (VisitTree.leaf 599 [1]) (VisitTree.leaf 602 [1]))) (VisitTree.branch 612 (VisitTree.branch 607 (VisitTree.leaf 605 [1]) (VisitTree.leaf 607 [1])) (VisitTree.branch 617 (VisitTree.leaf 612 [1]) (VisitTree.leaf 617 [1])))))))

def fastForwardChunkVisits118 (r : Nat) : List Nat :=
  forwardVisitTree118.lookup r

private theorem covered118 :
    visitsCovered forwardEventChunk118 forwardVisitTree118 = true := by
  decide +kernel

private theorem checked118 :
    visitsChecked forwardEventChunk118 forwardVisitTree118 = true := by
  decide +kernel

theorem eventVisits_forwardChunk118 (r : Nat) :
    eventVisits r forwardEventChunk118 = fastForwardChunkVisits118 r :=
  eventVisits_of_tree _ _ covered118 checked118 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk118

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 119. -/
def forwardVisitTree119 : VisitTree := (VisitTree.branch 508 (VisitTree.branch 359 (VisitTree.branch 281 (VisitTree.branch 253 (VisitTree.branch 251 (VisitTree.branch 232 (VisitTree.leaf 222 [1]) (VisitTree.leaf 232 [1])) (VisitTree.branch 252 (VisitTree.leaf 251 [1]) (VisitTree.leaf 252 [1]))) (VisitTree.branch 265 (VisitTree.branch 264 (VisitTree.leaf 253 [1]) (VisitTree.leaf 264 [1])) (VisitTree.branch 274 (VisitTree.leaf 265 [1]) (VisitTree.leaf 274 [1])))) (VisitTree.branch 320 (VisitTree.branch 309 (VisitTree.branch 286 (VisitTree.leaf 281 [1]) (VisitTree.leaf 286 [1])) (VisitTree.branch 313 (VisitTree.leaf 309 [1]) (VisitTree.leaf 313 [1]))) (VisitTree.branch 355 (VisitTree.branch 348 (VisitTree.leaf 320 [1]) (VisitTree.leaf 348 [1])) (VisitTree.branch 356 (VisitTree.leaf 355 [1]) (VisitTree.leaf 356 [1]))))) (VisitTree.branch 482 (VisitTree.branch 405 (VisitTree.branch 363 (VisitTree.branch 361 (VisitTree.leaf 359 [1]) (VisitTree.leaf 361 [1])) (VisitTree.branch 384 (VisitTree.leaf 363 [1]) (VisitTree.leaf 384 [1]))) (VisitTree.branch 426 (VisitTree.branch 420 (VisitTree.leaf 405 [1]) (VisitTree.leaf 420 [1])) (VisitTree.branch 456 (VisitTree.leaf 426 [1]) (VisitTree.leaf 456 [1])))) (VisitTree.branch 497 (VisitTree.branch 495 (VisitTree.branch 494 (VisitTree.leaf 482 [1]) (VisitTree.leaf 494 [1])) (VisitTree.branch 496 (VisitTree.leaf 495 [1]) (VisitTree.leaf 496 [1]))) (VisitTree.branch 502 (VisitTree.branch 500 (VisitTree.leaf 497 [1]) (VisitTree.leaf 500 [1])) (VisitTree.branch 505 (VisitTree.leaf 502 [1]) (VisitTree.leaf 505 [1])))))) (VisitTree.branch 541 (VisitTree.branch 526 (VisitTree.branch 518 (VisitTree.branch 515 (VisitTree.branch 512 (VisitTree.leaf 508 [1]) (VisitTree.leaf 512 [1])) (VisitTree.branch 517 (VisitTree.leaf 515 [1]) (VisitTree.leaf 517 [1]))) (VisitTree.branch 521 (VisitTree.branch 520 (VisitTree.leaf 518 [1]) (VisitTree.leaf 520 [1])) (VisitTree.branch 525 (VisitTree.leaf 521 [1]) (VisitTree.leaf 525 [1])))) (VisitTree.branch 534 (VisitTree.branch 532 (VisitTree.branch 530 (VisitTree.leaf 526 [1]) (VisitTree.leaf 530 [1])) (VisitTree.branch 533 (VisitTree.leaf 532 [1]) (VisitTree.leaf 533 [1]))) (VisitTree.branch 536 (VisitTree.branch 535 (VisitTree.leaf 534 [1]) (VisitTree.leaf 535 [1])) (VisitTree.branch 539 (VisitTree.leaf 536 [1]) (VisitTree.leaf 539 [1]))))) (VisitTree.branch 569 (VisitTree.branch 549 (VisitTree.branch 546 (VisitTree.branch 543 (VisitTree.leaf 541 [1]) (VisitTree.leaf 543 [1])) (VisitTree.branch 548 (VisitTree.leaf 546 [1]) (VisitTree.leaf 548 [1]))) (VisitTree.branch 555 (VisitTree.branch 550 (VisitTree.leaf 549 [1]) (VisitTree.leaf 550 [1])) (VisitTree.branch 561 (VisitTree.leaf 555 [1]) (VisitTree.leaf 561 [1])))) (VisitTree.branch 595 (VisitTree.branch 573 (VisitTree.branch 570 (VisitTree.leaf 569 [1]) (VisitTree.leaf 570 [1])) (VisitTree.branch 574 (VisitTree.leaf 573 [1]) (VisitTree.leaf 574 [1]))) (VisitTree.branch 601 (VisitTree.branch 600 (VisitTree.leaf 595 [1]) (VisitTree.leaf 600 [1])) (VisitTree.branch 606 (VisitTree.leaf 601 [1]) (VisitTree.leaf 606 [1])))))))

def fastForwardChunkVisits119 (r : Nat) : List Nat :=
  forwardVisitTree119.lookup r

private theorem covered119 :
    visitsCovered forwardEventChunk119 forwardVisitTree119 = true := by
  decide +kernel

private theorem checked119 :
    visitsChecked forwardEventChunk119 forwardVisitTree119 = true := by
  decide +kernel

theorem eventVisits_forwardChunk119 (r : Nat) :
    eventVisits r forwardEventChunk119 = fastForwardChunkVisits119 r :=
  eventVisits_of_tree _ _ covered119 checked119 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk119

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 120. -/
def forwardVisitTree120 : VisitTree := (VisitTree.branch 380 (VisitTree.branch 324 (VisitTree.branch 272 (VisitTree.branch 242 (VisitTree.branch 235 (VisitTree.branch 234 (VisitTree.leaf 223 [1]) (VisitTree.leaf 234 [1])) (VisitTree.branch 240 (VisitTree.leaf 235 [1]) (VisitTree.leaf 240 [1]))) (VisitTree.branch 246 (VisitTree.branch 243 (VisitTree.leaf 242 [1]) (VisitTree.leaf 243 [1])) (VisitTree.branch 256 (VisitTree.leaf 246 [1]) (VisitTree.leaf 256 [1])))) (VisitTree.branch 310 (VisitTree.branch 305 (VisitTree.branch 291 (VisitTree.leaf 272 [1]) (VisitTree.leaf 291 [1])) (VisitTree.branch 308 (VisitTree.leaf 305 [1]) (VisitTree.leaf 308 [1]))) (VisitTree.branch 321 (VisitTree.branch 312 (VisitTree.leaf 310 [1]) (VisitTree.leaf 312 [1])) (VisitTree.branch 323 (VisitTree.leaf 321 [1]) (VisitTree.leaf 323 [1]))))) (VisitTree.branch 345 (VisitTree.branch 336 (VisitTree.branch 326 (VisitTree.branch 325 (VisitTree.leaf 324 [1]) (VisitTree.leaf 325 [1])) (VisitTree.branch 329 (VisitTree.leaf 326 [1]) (VisitTree.leaf 329 [1]))) (VisitTree.branch 341 (VisitTree.branch 338 (VisitTree.leaf 336 [1]) (VisitTree.leaf 338 [1])) (VisitTree.branch 344 (VisitTree.leaf 341 [1]) (VisitTree.leaf 344 [1])))) (VisitTree.branch 366 (VisitTree.branch 354 (VisitTree.branch 347 (VisitTree.leaf 345 [1]) (VisitTree.leaf 347 [1])) (VisitTree.branch 364 (VisitTree.leaf 354 [1]) (VisitTree.leaf 364 [1]))) (VisitTree.branch 373 (VisitTree.branch 372 (VisitTree.leaf 366 [1]) (VisitTree.leaf 372 [1])) (VisitTree.branch 375 (VisitTree.leaf 373 [1]) (VisitTree.leaf 375 [1])))))) (VisitTree.branch 489 (VisitTree.branch 430 (VisitTree.branch 403 (VisitTree.branch 400 (VisitTree.branch 387 (VisitTree.leaf 380 [1]) (VisitTree.leaf 387 [1])) (VisitTree.branch 402 (VisitTree.leaf 400 [1]) (VisitTree.leaf 402 [1]))) (VisitTree.branch 417 (VisitTree.branch 409 (VisitTree.leaf 403 [1]) (VisitTree.leaf 409 [1])) (VisitTree.branch 421 (VisitTree.leaf 417 [1]) (VisitTree.leaf 421 [1])))) (VisitTree.branch 484 (VisitTree.branch 455 (VisitTree.branch 432 (VisitTree.leaf 430 [1]) (VisitTree.leaf 432 [1])) (VisitTree.branch 483 (VisitTree.leaf 455 [1]) (VisitTree.leaf 483 [1]))) (VisitTree.branch 486 (VisitTree.branch 485 (VisitTree.leaf 484 [1]) (VisitTree.leaf 485 [1])) (VisitTree.branch 488 (VisitTree.leaf 486 [1]) (VisitTree.leaf 488 [1]))))) (VisitTree.branch 504 (VisitTree.branch 498 (VisitTree.branch 491 (VisitTree.branch 490 (VisitTree.leaf 489 [1]) (VisitTree.leaf 490 [1])) (VisitTree.branch 493 (VisitTree.leaf 491 [1]) (VisitTree.leaf 493 [1]))) (VisitTree.branch 501 (VisitTree.branch 499 (VisitTree.leaf 498 [1]) (VisitTree.leaf 499 [1])) (VisitTree.branch 503 (VisitTree.leaf 501 [1]) (VisitTree.leaf 503 [1])))) (VisitTree.branch 510 (VisitTree.branch 507 (VisitTree.branch 506 (VisitTree.leaf 504 [1]) (VisitTree.leaf 506 [1])) (VisitTree.branch 509 (VisitTree.leaf 507 [1]) (VisitTree.leaf 509 [1]))) (VisitTree.branch 514 (VisitTree.branch 511 (VisitTree.leaf 510 [1]) (VisitTree.leaf 511 [1])) (VisitTree.branch 516 (VisitTree.leaf 514 [1]) (VisitTree.leaf 516 [1])))))))

def fastForwardChunkVisits120 (r : Nat) : List Nat :=
  forwardVisitTree120.lookup r

private theorem covered120 :
    visitsCovered forwardEventChunk120 forwardVisitTree120 = true := by
  decide +kernel

private theorem checked120 :
    visitsChecked forwardEventChunk120 forwardVisitTree120 = true := by
  decide +kernel

theorem eventVisits_forwardChunk120 (r : Nat) :
    eventVisits r forwardEventChunk120 = fastForwardChunkVisits120 r :=
  eventVisits_of_tree _ _ covered120 checked120 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk120

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 121. -/
def forwardVisitTree121 : VisitTree := (VisitTree.branch 598 (VisitTree.branch 552 (VisitTree.branch 351 (VisitTree.leaf 247 [1]) (VisitTree.branch 547 (VisitTree.leaf 351 [1]) (VisitTree.leaf 547 [1, 1, 1, 1, 1, 1, 1, 1]))) (VisitTree.branch 588 (VisitTree.leaf 552 [1, 1, 1]) (VisitTree.branch 597 (VisitTree.leaf 588 [1, 1, 1, 1, 1]) (VisitTree.leaf 597 [1, 1, 1, 1, 1])))) (VisitTree.branch 639 (VisitTree.branch 615 (VisitTree.leaf 598 [1, 1, 1, 1]) (VisitTree.branch 616 (VisitTree.leaf 615 [1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 616 [1, 1, 1, 1, 1]))) (VisitTree.branch 657 (VisitTree.branch 640 (VisitTree.leaf 639 [1, 1, 1, 1, 1, 1]) (VisitTree.leaf 640 [1, 1, 1, 1])) (VisitTree.branch 658 (VisitTree.leaf 657 [1, 1, 1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 658 [1, 1, 1, 1, 1, 1])))))

def fastForwardChunkVisits121 (r : Nat) : List Nat :=
  forwardVisitTree121.lookup r

private theorem covered121 :
    visitsCovered forwardEventChunk121 forwardVisitTree121 = true := by
  decide +kernel

private theorem checked121 :
    visitsChecked forwardEventChunk121 forwardVisitTree121 = true := by
  decide +kernel

theorem eventVisits_forwardChunk121 (r : Nat) :
    eventVisits r forwardEventChunk121 = fastForwardChunkVisits121 r :=
  eventVisits_of_tree _ _ covered121 checked121 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk121

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 122. -/
def forwardVisitTree122 : VisitTree := (VisitTree.branch 608 (VisitTree.branch 583 (VisitTree.branch 552 (VisitTree.branch 545 (VisitTree.leaf 542 [1, 1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 545 [1, 1])) (VisitTree.branch 578 (VisitTree.leaf 552 [1, 1, 1, 1]) (VisitTree.leaf 578 [1, 1, 1, 1, 1]))) (VisitTree.branch 601 (VisitTree.branch 598 (VisitTree.leaf 583 [1, 1, 1, 1, 1]) (VisitTree.leaf 598 [1, 1])) (VisitTree.branch 606 (VisitTree.leaf 601 [1]) (VisitTree.leaf 606 [1, 1, 1, 1, 1, 1, 1])))) (VisitTree.branch 629 (VisitTree.branch 616 (VisitTree.branch 611 (VisitTree.leaf 608 [1, 1, 1, 1, 1, 1]) (VisitTree.leaf 611 [1, 1])) (VisitTree.branch 626 (VisitTree.leaf 616 [1, 1]) (VisitTree.leaf 626 [1, 1]))) (VisitTree.branch 649 (VisitTree.branch 640 (VisitTree.leaf 629 [1, 1, 1, 1, 1, 1]) (VisitTree.leaf 640 [1, 1])) (VisitTree.branch 654 (VisitTree.leaf 649 [1, 1, 1, 1, 1, 1]) (VisitTree.branch 658 (VisitTree.leaf 654 [1, 1, 1]) (VisitTree.leaf 658 [1]))))))

def fastForwardChunkVisits122 (r : Nat) : List Nat :=
  forwardVisitTree122.lookup r

private theorem covered122 :
    visitsCovered forwardEventChunk122 forwardVisitTree122 = true := by
  decide +kernel

private theorem checked122 :
    visitsChecked forwardEventChunk122 forwardVisitTree122 = true := by
  decide +kernel

theorem eventVisits_forwardChunk122 (r : Nat) :
    eventVisits r forwardEventChunk122 = fastForwardChunkVisits122 r :=
  eventVisits_of_tree _ _ covered122 checked122 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk122

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 123. -/
def forwardVisitTree123 : VisitTree := (VisitTree.branch 611 (VisitTree.branch 581 (VisitTree.branch 545 (VisitTree.leaf 537 [1, 1, 1, 1]) (VisitTree.branch 573 (VisitTree.leaf 545 [1, 1, 1, 1, 1]) (VisitTree.leaf 573 [1, 1, 1, 1, 1, 1, 1, 1]))) (VisitTree.branch 590 (VisitTree.leaf 581 [1, 1, 1, 1, 1]) (VisitTree.branch 601 (VisitTree.leaf 590 [1, 1, 1, 1, 1, 1]) (VisitTree.leaf 601 [1, 1, 1, 1, 1])))) (VisitTree.branch 636 (VisitTree.branch 619 (VisitTree.leaf 611 [1, 1, 1, 1]) (VisitTree.branch 626 (VisitTree.leaf 619 [1, 1, 1, 1, 1, 1]) (VisitTree.leaf 626 [1, 1, 1, 1]))) (VisitTree.branch 647 (VisitTree.leaf 636 [1, 1, 1, 1, 1, 1]) (VisitTree.branch 654 (VisitTree.leaf 647 [1, 1, 1, 1, 1, 1]) (VisitTree.leaf 654 [1, 1, 1, 1, 1])))))

def fastForwardChunkVisits123 (r : Nat) : List Nat :=
  forwardVisitTree123.lookup r

private theorem covered123 :
    visitsCovered forwardEventChunk123 forwardVisitTree123 = true := by
  decide +kernel

private theorem checked123 :
    visitsChecked forwardEventChunk123 forwardVisitTree123 = true := by
  decide +kernel

theorem eventVisits_forwardChunk123 (r : Nat) :
    eventVisits r forwardEventChunk123 = fastForwardChunkVisits123 r :=
  eventVisits_of_tree _ _ covered123 checked123 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk123

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 124. -/
def forwardVisitTree124 : VisitTree := (VisitTree.branch 623 (VisitTree.branch 590 (VisitTree.branch 538 (VisitTree.branch 537 (VisitTree.leaf 529 [1, 1, 1]) (VisitTree.leaf 537 [1, 1, 1, 1])) (VisitTree.branch 574 (VisitTree.leaf 538 [1, 1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 574 [1, 1, 1, 1, 1, 1, 1, 1]))) (VisitTree.branch 605 (VisitTree.branch 593 (VisitTree.leaf 590 [1]) (VisitTree.leaf 593 [1, 1, 1, 1, 1, 1, 1])) (VisitTree.branch 619 (VisitTree.leaf 605 [1, 1, 1]) (VisitTree.leaf 619 [1])))) (VisitTree.branch 636 (VisitTree.branch 631 (VisitTree.branch 624 (VisitTree.leaf 623 [1, 1]) (VisitTree.leaf 624 [1, 1, 1, 1, 1, 1])) (VisitTree.branch 635 (VisitTree.leaf 631 [1, 1, 1, 1, 1, 1]) (VisitTree.leaf 635 [1, 1, 1]))) (VisitTree.branch 647 (VisitTree.branch 644 (VisitTree.leaf 636 [1]) (VisitTree.leaf 644 [1, 1, 1, 1, 1, 1, 1])) (VisitTree.branch 653 (VisitTree.leaf 647 [1]) (VisitTree.leaf 653 [1, 1, 1])))))

def fastForwardChunkVisits124 (r : Nat) : List Nat :=
  forwardVisitTree124.lookup r

private theorem covered124 :
    visitsCovered forwardEventChunk124 forwardVisitTree124 = true := by
  decide +kernel

private theorem checked124 :
    visitsChecked forwardEventChunk124 forwardVisitTree124 = true := by
  decide +kernel

theorem eventVisits_forwardChunk124 (r : Nat) :
    eventVisits r forwardEventChunk124 = fastForwardChunkVisits124 r :=
  eventVisits_of_tree _ _ covered124 checked124 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk124

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 125. -/
def forwardVisitTree125 : VisitTree := (VisitTree.branch 571 (VisitTree.branch 541 (VisitTree.branch 530 (VisitTree.leaf 529 [1, 1, 1, 1]) (VisitTree.branch 540 (VisitTree.leaf 530 [1, 1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 540 [1, 1, 1, 1, 1]))) (VisitTree.branch 569 (VisitTree.branch 568 (VisitTree.leaf 541 [1]) (VisitTree.leaf 568 [1])) (VisitTree.branch 570 (VisitTree.leaf 569 [1, 1, 1, 1, 1]) (VisitTree.leaf 570 [1, 1, 1, 1, 1])))) (VisitTree.branch 623 (VisitTree.branch 596 (VisitTree.leaf 571 [1, 1, 1, 1, 1, 1, 1]) (VisitTree.branch 605 (VisitTree.leaf 596 [1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 605 [1, 1, 1, 1]))) (VisitTree.branch 653 (VisitTree.branch 635 (VisitTree.leaf 623 [1, 1, 1, 1]) (VisitTree.leaf 635 [1, 1, 1, 1])) (VisitTree.branch 656 (VisitTree.leaf 653 [1, 1, 1]) (VisitTree.leaf 656 [1, 1, 1, 1, 1, 1])))))

def fastForwardChunkVisits125 (r : Nat) : List Nat :=
  forwardVisitTree125.lookup r

private theorem covered125 :
    visitsCovered forwardEventChunk125 forwardVisitTree125 = true := by
  decide +kernel

private theorem checked125 :
    visitsChecked forwardEventChunk125 forwardVisitTree125 = true := by
  decide +kernel

theorem eventVisits_forwardChunk125 (r : Nat) :
    eventVisits r forwardEventChunk125 = fastForwardChunkVisits125 r :=
  eventVisits_of_tree _ _ covered125 checked125 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk125

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 126. -/
def forwardVisitTree126 : VisitTree := (VisitTree.branch 577 (VisitTree.branch 546 (VisitTree.branch 532 (VisitTree.leaf 531 [1, 1, 1, 1, 1, 1, 1, 1]) (VisitTree.branch 541 (VisitTree.leaf 532 [1, 1, 1, 1]) (VisitTree.leaf 541 [1, 1, 1, 1, 1, 1]))) (VisitTree.branch 567 (VisitTree.leaf 546 [1, 1, 1]) (VisitTree.branch 568 (VisitTree.leaf 567 [1, 1, 1]) (VisitTree.leaf 568 [1, 1, 1, 1, 1, 1])))) (VisitTree.branch 617 (VisitTree.branch 582 (VisitTree.leaf 577 [1, 1, 1, 1, 1]) (VisitTree.branch 614 (VisitTree.leaf 582 [1, 1, 1, 1, 1]) (VisitTree.leaf 614 [1, 1, 1, 1, 1, 1]))) (VisitTree.branch 638 (VisitTree.leaf 617 [1, 1, 1, 1, 1, 1]) (VisitTree.branch 641 (VisitTree.leaf 638 [1, 1, 1, 1, 1]) (VisitTree.leaf 641 [1, 1, 1, 1, 1, 1, 1])))))

def fastForwardChunkVisits126 (r : Nat) : List Nat :=
  forwardVisitTree126.lookup r

private theorem covered126 :
    visitsCovered forwardEventChunk126 forwardVisitTree126 = true := by
  decide +kernel

private theorem checked126 :
    visitsChecked forwardEventChunk126 forwardVisitTree126 = true := by
  decide +kernel

theorem eventVisits_forwardChunk126 (r : Nat) :
    eventVisits r forwardEventChunk126 = fastForwardChunkVisits126 r :=
  eventVisits_of_tree _ _ covered126 checked126 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk126

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 127. -/
def forwardVisitTree127 : VisitTree := (VisitTree.branch 577 (VisitTree.branch 546 (VisitTree.branch 534 (VisitTree.branch 533 (VisitTree.leaf 532 [1, 1, 1, 1]) (VisitTree.leaf 533 [1, 1, 1, 1, 1, 1, 1, 1])) (VisitTree.branch 535 (VisitTree.leaf 534 [1, 1, 1, 1]) (VisitTree.leaf 535 [1, 1, 1, 1, 1]))) (VisitTree.branch 566 (VisitTree.branch 565 (VisitTree.leaf 546 [1, 1, 1]) (VisitTree.leaf 565 [1, 1, 1, 1])) (VisitTree.branch 567 (VisitTree.leaf 566 [1, 1, 1]) (VisitTree.branch 576 (VisitTree.leaf 567 [1, 1]) (VisitTree.leaf 576 [1, 1, 1, 1, 1]))))) (VisitTree.branch 620 (VisitTree.branch 602 (VisitTree.branch 599 (VisitTree.leaf 577 [1]) (VisitTree.leaf 599 [1, 1, 1, 1, 1, 1])) (VisitTree.branch 614 (VisitTree.leaf 602 [1]) (VisitTree.leaf 614 [1]))) (VisitTree.branch 638 (VisitTree.branch 632 (VisitTree.leaf 620 [1, 1, 1]) (VisitTree.leaf 632 [1, 1, 1])) (VisitTree.branch 650 (VisitTree.leaf 638 [1]) (VisitTree.branch 659 (VisitTree.leaf 650 [1, 1, 1, 1, 1]) (VisitTree.leaf 659 [1, 1, 1, 1, 1]))))))

def fastForwardChunkVisits127 (r : Nat) : List Nat :=
  forwardVisitTree127.lookup r

private theorem covered127 :
    visitsCovered forwardEventChunk127 forwardVisitTree127 = true := by
  decide +kernel

private theorem checked127 :
    visitsChecked forwardEventChunk127 forwardVisitTree127 = true := by
  decide +kernel

theorem eventVisits_forwardChunk127 (r : Nat) :
    eventVisits r forwardEventChunk127 = fastForwardChunkVisits127 r :=
  eventVisits_of_tree _ _ covered127 checked127 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk127

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 128. -/
def forwardVisitTree128 : VisitTree := (VisitTree.branch 595 (VisitTree.branch 560 (VisitTree.branch 534 (VisitTree.branch 524 (VisitTree.leaf 523 [1, 1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 524 [1, 1])) (VisitTree.branch 549 (VisitTree.leaf 534 [1, 1, 1, 1]) (VisitTree.leaf 549 [1, 1, 1, 1, 1]))) (VisitTree.branch 565 (VisitTree.branch 564 (VisitTree.leaf 560 [1, 1]) (VisitTree.leaf 564 [1, 1, 1])) (VisitTree.branch 586 (VisitTree.leaf 565 [1]) (VisitTree.leaf 586 [1, 1, 1, 1, 1])))) (VisitTree.branch 621 (VisitTree.branch 609 (VisitTree.branch 602 (VisitTree.leaf 595 [1]) (VisitTree.leaf 602 [1, 1, 1, 1])) (VisitTree.branch 620 (VisitTree.leaf 609 [1, 1, 1, 1]) (VisitTree.leaf 620 [1, 1, 1]))) (VisitTree.branch 632 (VisitTree.branch 628 (VisitTree.leaf 621 [1, 1, 1, 1, 1, 1]) (VisitTree.leaf 628 [1])) (VisitTree.branch 633 (VisitTree.leaf 632 [1, 1, 1]) (VisitTree.branch 650 (VisitTree.leaf 633 [1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 650 [1, 1, 1, 1, 1]))))))

def fastForwardChunkVisits128 (r : Nat) : List Nat :=
  forwardVisitTree128.lookup r

private theorem covered128 :
    visitsCovered forwardEventChunk128 forwardVisitTree128 = true := by
  decide +kernel

private theorem checked128 :
    visitsChecked forwardEventChunk128 forwardVisitTree128 = true := by
  decide +kernel

theorem eventVisits_forwardChunk128 (r : Nat) :
    eventVisits r forwardEventChunk128 = fastForwardChunkVisits128 r :=
  eventVisits_of_tree _ _ covered128 checked128 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk128

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 129. -/
def forwardVisitTree129 : VisitTree := (VisitTree.branch 594 (VisitTree.branch 560 (VisitTree.branch 525 (VisitTree.leaf 524 [1, 1, 1, 1, 1, 1]) (VisitTree.branch 544 (VisitTree.leaf 525 [1, 1, 1, 1]) (VisitTree.leaf 544 [1, 1, 1]))) (VisitTree.branch 561 (VisitTree.leaf 560 [1, 1, 1]) (VisitTree.branch 580 (VisitTree.leaf 561 [1, 1, 1, 1, 1]) (VisitTree.leaf 580 [1, 1, 1, 1, 1, 1])))) (VisitTree.branch 628 (VisitTree.branch 595 (VisitTree.leaf 594 [1, 1, 1, 1, 1, 1, 1]) (VisitTree.branch 609 (VisitTree.leaf 595 [1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 609 [1, 1, 1]))) (VisitTree.branch 643 (VisitTree.leaf 628 [1, 1, 1, 1, 1, 1]) (VisitTree.branch 660 (VisitTree.leaf 643 [1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 660 [1, 1, 1, 1, 1, 1, 1])))))

def fastForwardChunkVisits129 (r : Nat) : List Nat :=
  forwardVisitTree129.lookup r

private theorem covered129 :
    visitsCovered forwardEventChunk129 forwardVisitTree129 = true := by
  decide +kernel

private theorem checked129 :
    visitsChecked forwardEventChunk129 forwardVisitTree129 = true := by
  decide +kernel

theorem eventVisits_forwardChunk129 (r : Nat) :
    eventVisits r forwardEventChunk129 = fastForwardChunkVisits129 r :=
  eventVisits_of_tree _ _ covered129 checked129 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk129

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 130. -/
def forwardVisitTree130 : VisitTree := (VisitTree.branch 589 (VisitTree.branch 544 (VisitTree.branch 527 (VisitTree.branch 526 (VisitTree.leaf 525 [1, 1, 1, 1]) (VisitTree.leaf 526 [1, 1, 1, 1, 1, 1, 1])) (VisitTree.branch 543 (VisitTree.leaf 527 [1, 1, 1]) (VisitTree.leaf 543 [1, 1, 1, 1, 1, 1, 1, 1]))) (VisitTree.branch 579 (VisitTree.branch 562 (VisitTree.leaf 544 [1, 1]) (VisitTree.leaf 562 [1, 1, 1, 1, 1, 1])) (VisitTree.branch 580 (VisitTree.leaf 579 [1, 1, 1, 1, 1, 1]) (VisitTree.leaf 580 [1, 1])))) (VisitTree.branch 627 (VisitTree.branch 600 (VisitTree.branch 594 (VisitTree.leaf 589 [1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 594 [1])) (VisitTree.branch 610 (VisitTree.leaf 600 [1, 1, 1]) (VisitTree.leaf 610 [1, 1]))) (VisitTree.branch 648 (VisitTree.branch 643 (VisitTree.leaf 627 [1, 1]) (VisitTree.leaf 643 [1])) (VisitTree.branch 655 (VisitTree.leaf 648 [1, 1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 655 [1, 1])))))

def fastForwardChunkVisits130 (r : Nat) : List Nat :=
  forwardVisitTree130.lookup r

private theorem covered130 :
    visitsCovered forwardEventChunk130 forwardVisitTree130 = true := by
  decide +kernel

private theorem checked130 :
    visitsChecked forwardEventChunk130 forwardVisitTree130 = true := by
  decide +kernel

theorem eventVisits_forwardChunk130 (r : Nat) :
    eventVisits r forwardEventChunk130 = fastForwardChunkVisits130 r :=
  eventVisits_of_tree _ _ covered130 checked130 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk130

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 131. -/
def forwardVisitTree131 : VisitTree := (VisitTree.branch 584 (VisitTree.branch 551 (VisitTree.branch 528 (VisitTree.branch 527 (VisitTree.leaf 517 [1, 1]) (VisitTree.leaf 527 [1, 1, 1, 1])) (VisitTree.branch 550 (VisitTree.leaf 528 [1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 550 [1, 1, 1, 1, 1, 1]))) (VisitTree.branch 559 (VisitTree.branch 558 (VisitTree.leaf 551 [1, 1]) (VisitTree.leaf 558 [1])) (VisitTree.branch 563 (VisitTree.leaf 559 [1, 1, 1, 1, 1]) (VisitTree.leaf 563 [1, 1, 1, 1, 1])))) (VisitTree.branch 610 (VisitTree.branch 600 (VisitTree.branch 585 (VisitTree.leaf 584 [1, 1]) (VisitTree.leaf 585 [1, 1])) (VisitTree.branch 603 (VisitTree.leaf 600 [1, 1, 1, 1]) (VisitTree.leaf 603 [1]))) (VisitTree.branch 627 (VisitTree.branch 622 (VisitTree.leaf 610 [1, 1, 1, 1]) (VisitTree.leaf 622 [1, 1, 1, 1, 1])) (VisitTree.branch 634 (VisitTree.leaf 627 [1, 1, 1, 1, 1]) (VisitTree.branch 655 (VisitTree.leaf 634 [1, 1, 1, 1, 1]) (VisitTree.leaf 655 [1, 1, 1, 1]))))))

def fastForwardChunkVisits131 (r : Nat) : List Nat :=
  forwardVisitTree131.lookup r

private theorem covered131 :
    visitsCovered forwardEventChunk131 forwardVisitTree131 = true := by
  decide +kernel

private theorem checked131 :
    visitsChecked forwardEventChunk131 forwardVisitTree131 = true := by
  decide +kernel

theorem eventVisits_forwardChunk131 (r : Nat) :
    eventVisits r forwardEventChunk131 = fastForwardChunkVisits131 r :=
  eventVisits_of_tree _ _ covered131 checked131 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk131


