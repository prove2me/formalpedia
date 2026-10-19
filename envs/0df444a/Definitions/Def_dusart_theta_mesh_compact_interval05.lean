-- Prove2me | Definitions.Def_dusart_theta_mesh_compact_interval05
-- name    : dusart_theta_mesh_compact_interval05
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-17T02:59:39.853684+00:00
-- url     : https://prove2.me/theorems/35dd9d1f-2ddb-4faa-bd6d-4c6480d58b12
-- title:
--   Certified theta upper interval from 6441787648 to 8052400384
-- statement:
--   Put $a=6441787648$, $b=8052400384$, $u=6441698088936622$, and $v=8052306946255057$. The Chebyshev theta function satisfies
--
--   $$10^6\theta(a)\le u\ \Longrightarrow\ \left(10^6\theta(b)\le v\quad\text{and}\quad\forall x\in[a,b),\ \theta(x)\le x+100000+x/10000\right).$$
--
--   This certifies one contiguous interval of the upper bound used in the finite fourth-power logarithmic theta estimate. The endpoint carry can be passed to the next interval.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Complete finite interval certificate.

import Definitions.Def_dusart_theta_mesh_compact_soundness
import Theorems.Thm_dusart_theta_mesh_generic_group480
import Theorems.Thm_dusart_theta_mesh_generic_group481
import Theorems.Thm_dusart_theta_mesh_generic_group482
import Theorems.Thm_dusart_theta_mesh_generic_group483
import Theorems.Thm_dusart_theta_mesh_generic_group484
import Theorems.Thm_dusart_theta_mesh_generic_group485
import Theorems.Thm_dusart_theta_mesh_generic_group486
import Theorems.Thm_dusart_theta_mesh_generic_group487
import Theorems.Thm_dusart_theta_mesh_generic_group488
import Theorems.Thm_dusart_theta_mesh_generic_group489
import Theorems.Thm_dusart_theta_mesh_generic_group490
import Theorems.Thm_dusart_theta_mesh_generic_group491
import Theorems.Thm_dusart_theta_mesh_generic_group492
import Theorems.Thm_dusart_theta_mesh_generic_group493
import Theorems.Thm_dusart_theta_mesh_generic_group494
import Theorems.Thm_dusart_theta_mesh_generic_group495
import Theorems.Thm_dusart_theta_mesh_generic_group496
import Theorems.Thm_dusart_theta_mesh_generic_group497
import Theorems.Thm_dusart_theta_mesh_generic_group498
import Theorems.Thm_dusart_theta_mesh_generic_group499
import Theorems.Thm_dusart_theta_mesh_generic_group500
import Theorems.Thm_dusart_theta_mesh_generic_group501
import Theorems.Thm_dusart_theta_mesh_generic_group502
import Theorems.Thm_dusart_theta_mesh_generic_group503
import Theorems.Thm_dusart_theta_mesh_generic_group504
import Theorems.Thm_dusart_theta_mesh_generic_group505
import Theorems.Thm_dusart_theta_mesh_generic_group506
import Theorems.Thm_dusart_theta_mesh_generic_group507
import Theorems.Thm_dusart_theta_mesh_generic_group508
import Theorems.Thm_dusart_theta_mesh_generic_group509
import Theorems.Thm_dusart_theta_mesh_generic_group510
import Theorems.Thm_dusart_theta_mesh_generic_group511
import Theorems.Thm_dusart_theta_mesh_generic_group512
import Theorems.Thm_dusart_theta_mesh_generic_group513
import Theorems.Thm_dusart_theta_mesh_generic_group514
import Theorems.Thm_dusart_theta_mesh_generic_group515
import Theorems.Thm_dusart_theta_mesh_generic_group516
import Theorems.Thm_dusart_theta_mesh_generic_group517
import Theorems.Thm_dusart_theta_mesh_generic_group518
import Theorems.Thm_dusart_theta_mesh_generic_group519
import Theorems.Thm_dusart_theta_mesh_generic_group520
import Theorems.Thm_dusart_theta_mesh_generic_group521
import Theorems.Thm_dusart_theta_mesh_generic_group522
import Theorems.Thm_dusart_theta_mesh_generic_group523
import Theorems.Thm_dusart_theta_mesh_generic_group524
import Theorems.Thm_dusart_theta_mesh_generic_group525
import Theorems.Thm_dusart_theta_mesh_generic_group526
import Theorems.Thm_dusart_theta_mesh_generic_group527
import Theorems.Thm_dusart_theta_mesh_generic_group528
import Theorems.Thm_dusart_theta_mesh_generic_group529
import Theorems.Thm_dusart_theta_mesh_generic_group530
import Theorems.Thm_dusart_theta_mesh_generic_group531
import Theorems.Thm_dusart_theta_mesh_generic_group532
import Theorems.Thm_dusart_theta_mesh_generic_group533
import Theorems.Thm_dusart_theta_mesh_generic_group534
import Theorems.Thm_dusart_theta_mesh_generic_group535
import Theorems.Thm_dusart_theta_mesh_generic_group536
import Theorems.Thm_dusart_theta_mesh_generic_group537
import Theorems.Thm_dusart_theta_mesh_generic_group538
import Theorems.Thm_dusart_theta_mesh_generic_group539
import Theorems.Thm_dusart_theta_mesh_generic_group540
import Theorems.Thm_dusart_theta_mesh_generic_group541
import Theorems.Thm_dusart_theta_mesh_generic_group542
import Theorems.Thm_dusart_theta_mesh_generic_group543
import Theorems.Thm_dusart_theta_mesh_generic_group544
import Theorems.Thm_dusart_theta_mesh_generic_group545
import Theorems.Thm_dusart_theta_mesh_generic_group546
import Theorems.Thm_dusart_theta_mesh_generic_group547
import Theorems.Thm_dusart_theta_mesh_generic_group548
import Theorems.Thm_dusart_theta_mesh_generic_group549
import Theorems.Thm_dusart_theta_mesh_generic_group550
import Theorems.Thm_dusart_theta_mesh_generic_group551
import Theorems.Thm_dusart_theta_mesh_generic_group552
import Theorems.Thm_dusart_theta_mesh_generic_group553
import Theorems.Thm_dusart_theta_mesh_generic_group554
import Theorems.Thm_dusart_theta_mesh_generic_group555
import Theorems.Thm_dusart_theta_mesh_generic_group556
import Theorems.Thm_dusart_theta_mesh_generic_group557
import Theorems.Thm_dusart_theta_mesh_generic_group558
import Theorems.Thm_dusart_theta_mesh_generic_group559
import Theorems.Thm_dusart_theta_mesh_generic_group560
import Theorems.Thm_dusart_theta_mesh_generic_group561
import Theorems.Thm_dusart_theta_mesh_generic_group562
import Theorems.Thm_dusart_theta_mesh_generic_group563
import Theorems.Thm_dusart_theta_mesh_generic_group564
import Theorems.Thm_dusart_theta_mesh_generic_group565
import Theorems.Thm_dusart_theta_mesh_generic_group566
import Theorems.Thm_dusart_theta_mesh_generic_group567
import Theorems.Thm_dusart_theta_mesh_generic_group568
import Theorems.Thm_dusart_theta_mesh_generic_group569
import Theorems.Thm_dusart_theta_mesh_generic_group570
import Theorems.Thm_dusart_theta_mesh_generic_group571
import Theorems.Thm_dusart_theta_mesh_generic_group572
import Theorems.Thm_dusart_theta_mesh_generic_group573
import Theorems.Thm_dusart_theta_mesh_generic_group574
import Theorems.Thm_dusart_theta_mesh_generic_group575
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartCompactIntervals
theorem interval5_generic : DusartNumeric.GenericSpec 6441787648 8052400384 6441698088936622 8052306946255057 := by
 intro S step compose
 exact (compose (compose (compose (compose (compose (compose (dusart_theta_mesh_generic_group480 S step @compose) (compose (dusart_theta_mesh_generic_group481 S step @compose) (dusart_theta_mesh_generic_group482 S step @compose))) (compose (dusart_theta_mesh_generic_group483 S step @compose) (compose (dusart_theta_mesh_generic_group484 S step @compose) (dusart_theta_mesh_generic_group485 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group486 S step @compose) (compose (dusart_theta_mesh_generic_group487 S step @compose) (dusart_theta_mesh_generic_group488 S step @compose))) (compose (dusart_theta_mesh_generic_group489 S step @compose) (compose (dusart_theta_mesh_generic_group490 S step @compose) (dusart_theta_mesh_generic_group491 S step @compose))))) (compose (compose (compose (dusart_theta_mesh_generic_group492 S step @compose) (compose (dusart_theta_mesh_generic_group493 S step @compose) (dusart_theta_mesh_generic_group494 S step @compose))) (compose (dusart_theta_mesh_generic_group495 S step @compose) (compose (dusart_theta_mesh_generic_group496 S step @compose) (dusart_theta_mesh_generic_group497 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group498 S step @compose) (compose (dusart_theta_mesh_generic_group499 S step @compose) (dusart_theta_mesh_generic_group500 S step @compose))) (compose (dusart_theta_mesh_generic_group501 S step @compose) (compose (dusart_theta_mesh_generic_group502 S step @compose) (dusart_theta_mesh_generic_group503 S step @compose)))))) (compose (compose (compose (compose (dusart_theta_mesh_generic_group504 S step @compose) (compose (dusart_theta_mesh_generic_group505 S step @compose) (dusart_theta_mesh_generic_group506 S step @compose))) (compose (dusart_theta_mesh_generic_group507 S step @compose) (compose (dusart_theta_mesh_generic_group508 S step @compose) (dusart_theta_mesh_generic_group509 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group510 S step @compose) (compose (dusart_theta_mesh_generic_group511 S step @compose) (dusart_theta_mesh_generic_group512 S step @compose))) (compose (dusart_theta_mesh_generic_group513 S step @compose) (compose (dusart_theta_mesh_generic_group514 S step @compose) (dusart_theta_mesh_generic_group515 S step @compose))))) (compose (compose (compose (dusart_theta_mesh_generic_group516 S step @compose) (compose (dusart_theta_mesh_generic_group517 S step @compose) (dusart_theta_mesh_generic_group518 S step @compose))) (compose (dusart_theta_mesh_generic_group519 S step @compose) (compose (dusart_theta_mesh_generic_group520 S step @compose) (dusart_theta_mesh_generic_group521 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group522 S step @compose) (compose (dusart_theta_mesh_generic_group523 S step @compose) (dusart_theta_mesh_generic_group524 S step @compose))) (compose (dusart_theta_mesh_generic_group525 S step @compose) (compose (dusart_theta_mesh_generic_group526 S step @compose) (dusart_theta_mesh_generic_group527 S step @compose))))))) (compose (compose (compose (compose (compose (dusart_theta_mesh_generic_group528 S step @compose) (compose (dusart_theta_mesh_generic_group529 S step @compose) (dusart_theta_mesh_generic_group530 S step @compose))) (compose (dusart_theta_mesh_generic_group531 S step @compose) (compose (dusart_theta_mesh_generic_group532 S step @compose) (dusart_theta_mesh_generic_group533 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group534 S step @compose) (compose (dusart_theta_mesh_generic_group535 S step @compose) (dusart_theta_mesh_generic_group536 S step @compose))) (compose (dusart_theta_mesh_generic_group537 S step @compose) (compose (dusart_theta_mesh_generic_group538 S step @compose) (dusart_theta_mesh_generic_group539 S step @compose))))) (compose (compose (compose (dusart_theta_mesh_generic_group540 S step @compose) (compose (dusart_theta_mesh_generic_group541 S step @compose) (dusart_theta_mesh_generic_group542 S step @compose))) (compose (dusart_theta_mesh_generic_group543 S step @compose) (compose (dusart_theta_mesh_generic_group544 S step @compose) (dusart_theta_mesh_generic_group545 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group546 S step @compose) (compose (dusart_theta_mesh_generic_group547 S step @compose) (dusart_theta_mesh_generic_group548 S step @compose))) (compose (dusart_theta_mesh_generic_group549 S step @compose) (compose (dusart_theta_mesh_generic_group550 S step @compose) (dusart_theta_mesh_generic_group551 S step @compose)))))) (compose (compose (compose (compose (dusart_theta_mesh_generic_group552 S step @compose) (compose (dusart_theta_mesh_generic_group553 S step @compose) (dusart_theta_mesh_generic_group554 S step @compose))) (compose (dusart_theta_mesh_generic_group555 S step @compose) (compose (dusart_theta_mesh_generic_group556 S step @compose) (dusart_theta_mesh_generic_group557 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group558 S step @compose) (compose (dusart_theta_mesh_generic_group559 S step @compose) (dusart_theta_mesh_generic_group560 S step @compose))) (compose (dusart_theta_mesh_generic_group561 S step @compose) (compose (dusart_theta_mesh_generic_group562 S step @compose) (dusart_theta_mesh_generic_group563 S step @compose))))) (compose (compose (compose (dusart_theta_mesh_generic_group564 S step @compose) (compose (dusart_theta_mesh_generic_group565 S step @compose) (dusart_theta_mesh_generic_group566 S step @compose))) (compose (dusart_theta_mesh_generic_group567 S step @compose) (compose (dusart_theta_mesh_generic_group568 S step @compose) (dusart_theta_mesh_generic_group569 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group570 S step @compose) (compose (dusart_theta_mesh_generic_group571 S step @compose) (dusart_theta_mesh_generic_group572 S step @compose))) (compose (dusart_theta_mesh_generic_group573 S step @compose) (compose (dusart_theta_mesh_generic_group574 S step @compose) (dusart_theta_mesh_generic_group575 S step @compose))))))))
theorem interval5 : DusartMeshUpper.Literal.Spec 6441787648 8052400384 6441698088936622 8052306946255057 :=
 DusartProvedBridge.interpret interval5_generic
end DusartCompactIntervals


