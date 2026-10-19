-- Prove2me | Definitions.Def_dusart_theta_mesh_compact_interval06
-- name    : dusart_theta_mesh_compact_interval06
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-17T03:00:09.489169+00:00
-- url     : https://prove2.me/theorems/85edd385-7266-4e6e-90e0-fa161e323ef5
-- title:
--   Certified theta upper interval from 8052400384 to 9663013120
-- statement:
--   Put $a=8052400384$, $b=9663013120$, $u=8052306946255057$, and $v=9662936651771238$. The Chebyshev theta function satisfies
--
--   $$10^6\theta(a)\le u\ \Longrightarrow\ \left(10^6\theta(b)\le v\quad\text{and}\quad\forall x\in[a,b),\ \theta(x)\le x+100000+x/10000\right).$$
--
--   This certifies one contiguous interval of the upper bound used in the finite fourth-power logarithmic theta estimate. The endpoint carry can be passed to the next interval.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Complete finite interval certificate.

import Definitions.Def_dusart_theta_mesh_compact_soundness
import Theorems.Thm_dusart_theta_mesh_generic_group576
import Theorems.Thm_dusart_theta_mesh_generic_group577
import Theorems.Thm_dusart_theta_mesh_generic_group578
import Theorems.Thm_dusart_theta_mesh_generic_group579
import Theorems.Thm_dusart_theta_mesh_generic_group580
import Theorems.Thm_dusart_theta_mesh_generic_group581
import Theorems.Thm_dusart_theta_mesh_generic_group582
import Theorems.Thm_dusart_theta_mesh_generic_group583
import Theorems.Thm_dusart_theta_mesh_generic_group584
import Theorems.Thm_dusart_theta_mesh_generic_group585
import Theorems.Thm_dusart_theta_mesh_generic_group586
import Theorems.Thm_dusart_theta_mesh_generic_group587
import Theorems.Thm_dusart_theta_mesh_generic_group588
import Theorems.Thm_dusart_theta_mesh_generic_group589
import Theorems.Thm_dusart_theta_mesh_generic_group590
import Theorems.Thm_dusart_theta_mesh_generic_group591
import Theorems.Thm_dusart_theta_mesh_generic_group592
import Theorems.Thm_dusart_theta_mesh_generic_group593
import Theorems.Thm_dusart_theta_mesh_generic_group594
import Theorems.Thm_dusart_theta_mesh_generic_group595
import Theorems.Thm_dusart_theta_mesh_generic_group596
import Theorems.Thm_dusart_theta_mesh_generic_group597
import Theorems.Thm_dusart_theta_mesh_generic_group598
import Theorems.Thm_dusart_theta_mesh_generic_group599
import Theorems.Thm_dusart_theta_mesh_generic_group600
import Theorems.Thm_dusart_theta_mesh_generic_group601
import Theorems.Thm_dusart_theta_mesh_generic_group602
import Theorems.Thm_dusart_theta_mesh_generic_group603
import Theorems.Thm_dusart_theta_mesh_generic_group604
import Theorems.Thm_dusart_theta_mesh_generic_group605
import Theorems.Thm_dusart_theta_mesh_generic_group606
import Theorems.Thm_dusart_theta_mesh_generic_group607
import Theorems.Thm_dusart_theta_mesh_generic_group608
import Theorems.Thm_dusart_theta_mesh_generic_group609
import Theorems.Thm_dusart_theta_mesh_generic_group610
import Theorems.Thm_dusart_theta_mesh_generic_group611
import Theorems.Thm_dusart_theta_mesh_generic_group612
import Theorems.Thm_dusart_theta_mesh_generic_group613
import Theorems.Thm_dusart_theta_mesh_generic_group614
import Theorems.Thm_dusart_theta_mesh_generic_group615
import Theorems.Thm_dusart_theta_mesh_generic_group616
import Theorems.Thm_dusart_theta_mesh_generic_group617
import Theorems.Thm_dusart_theta_mesh_generic_group618
import Theorems.Thm_dusart_theta_mesh_generic_group619
import Theorems.Thm_dusart_theta_mesh_generic_group620
import Theorems.Thm_dusart_theta_mesh_generic_group621
import Theorems.Thm_dusart_theta_mesh_generic_group622
import Theorems.Thm_dusart_theta_mesh_generic_group623
import Theorems.Thm_dusart_theta_mesh_generic_group624
import Theorems.Thm_dusart_theta_mesh_generic_group625
import Theorems.Thm_dusart_theta_mesh_generic_group626
import Theorems.Thm_dusart_theta_mesh_generic_group627
import Theorems.Thm_dusart_theta_mesh_generic_group628
import Theorems.Thm_dusart_theta_mesh_generic_group629
import Theorems.Thm_dusart_theta_mesh_generic_group630
import Theorems.Thm_dusart_theta_mesh_generic_group631
import Theorems.Thm_dusart_theta_mesh_generic_group632
import Theorems.Thm_dusart_theta_mesh_generic_group633
import Theorems.Thm_dusart_theta_mesh_generic_group634
import Theorems.Thm_dusart_theta_mesh_generic_group635
import Theorems.Thm_dusart_theta_mesh_generic_group636
import Theorems.Thm_dusart_theta_mesh_generic_group637
import Theorems.Thm_dusart_theta_mesh_generic_group638
import Theorems.Thm_dusart_theta_mesh_generic_group639
import Theorems.Thm_dusart_theta_mesh_generic_group640
import Theorems.Thm_dusart_theta_mesh_generic_group641
import Theorems.Thm_dusart_theta_mesh_generic_group642
import Theorems.Thm_dusart_theta_mesh_generic_group643
import Theorems.Thm_dusart_theta_mesh_generic_group644
import Theorems.Thm_dusart_theta_mesh_generic_group645
import Theorems.Thm_dusart_theta_mesh_generic_group646
import Theorems.Thm_dusart_theta_mesh_generic_group647
import Theorems.Thm_dusart_theta_mesh_generic_group648
import Theorems.Thm_dusart_theta_mesh_generic_group649
import Theorems.Thm_dusart_theta_mesh_generic_group650
import Theorems.Thm_dusart_theta_mesh_generic_group651
import Theorems.Thm_dusart_theta_mesh_generic_group652
import Theorems.Thm_dusart_theta_mesh_generic_group653
import Theorems.Thm_dusart_theta_mesh_generic_group654
import Theorems.Thm_dusart_theta_mesh_generic_group655
import Theorems.Thm_dusart_theta_mesh_generic_group656
import Theorems.Thm_dusart_theta_mesh_generic_group657
import Theorems.Thm_dusart_theta_mesh_generic_group658
import Theorems.Thm_dusart_theta_mesh_generic_group659
import Theorems.Thm_dusart_theta_mesh_generic_group660
import Theorems.Thm_dusart_theta_mesh_generic_group661
import Theorems.Thm_dusart_theta_mesh_generic_group662
import Theorems.Thm_dusart_theta_mesh_generic_group663
import Theorems.Thm_dusart_theta_mesh_generic_group664
import Theorems.Thm_dusart_theta_mesh_generic_group665
import Theorems.Thm_dusart_theta_mesh_generic_group666
import Theorems.Thm_dusart_theta_mesh_generic_group667
import Theorems.Thm_dusart_theta_mesh_generic_group668
import Theorems.Thm_dusart_theta_mesh_generic_group669
import Theorems.Thm_dusart_theta_mesh_generic_group670
import Theorems.Thm_dusart_theta_mesh_generic_group671
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartCompactIntervals
theorem interval6_generic : DusartNumeric.GenericSpec 8052400384 9663013120 8052306946255057 9662936651771238 := by
 intro S step compose
 exact (compose (compose (compose (compose (compose (compose (dusart_theta_mesh_generic_group576 S step @compose) (compose (dusart_theta_mesh_generic_group577 S step @compose) (dusart_theta_mesh_generic_group578 S step @compose))) (compose (dusart_theta_mesh_generic_group579 S step @compose) (compose (dusart_theta_mesh_generic_group580 S step @compose) (dusart_theta_mesh_generic_group581 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group582 S step @compose) (compose (dusart_theta_mesh_generic_group583 S step @compose) (dusart_theta_mesh_generic_group584 S step @compose))) (compose (dusart_theta_mesh_generic_group585 S step @compose) (compose (dusart_theta_mesh_generic_group586 S step @compose) (dusart_theta_mesh_generic_group587 S step @compose))))) (compose (compose (compose (dusart_theta_mesh_generic_group588 S step @compose) (compose (dusart_theta_mesh_generic_group589 S step @compose) (dusart_theta_mesh_generic_group590 S step @compose))) (compose (dusart_theta_mesh_generic_group591 S step @compose) (compose (dusart_theta_mesh_generic_group592 S step @compose) (dusart_theta_mesh_generic_group593 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group594 S step @compose) (compose (dusart_theta_mesh_generic_group595 S step @compose) (dusart_theta_mesh_generic_group596 S step @compose))) (compose (dusart_theta_mesh_generic_group597 S step @compose) (compose (dusart_theta_mesh_generic_group598 S step @compose) (dusart_theta_mesh_generic_group599 S step @compose)))))) (compose (compose (compose (compose (dusart_theta_mesh_generic_group600 S step @compose) (compose (dusart_theta_mesh_generic_group601 S step @compose) (dusart_theta_mesh_generic_group602 S step @compose))) (compose (dusart_theta_mesh_generic_group603 S step @compose) (compose (dusart_theta_mesh_generic_group604 S step @compose) (dusart_theta_mesh_generic_group605 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group606 S step @compose) (compose (dusart_theta_mesh_generic_group607 S step @compose) (dusart_theta_mesh_generic_group608 S step @compose))) (compose (dusart_theta_mesh_generic_group609 S step @compose) (compose (dusart_theta_mesh_generic_group610 S step @compose) (dusart_theta_mesh_generic_group611 S step @compose))))) (compose (compose (compose (dusart_theta_mesh_generic_group612 S step @compose) (compose (dusart_theta_mesh_generic_group613 S step @compose) (dusart_theta_mesh_generic_group614 S step @compose))) (compose (dusart_theta_mesh_generic_group615 S step @compose) (compose (dusart_theta_mesh_generic_group616 S step @compose) (dusart_theta_mesh_generic_group617 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group618 S step @compose) (compose (dusart_theta_mesh_generic_group619 S step @compose) (dusart_theta_mesh_generic_group620 S step @compose))) (compose (dusart_theta_mesh_generic_group621 S step @compose) (compose (dusart_theta_mesh_generic_group622 S step @compose) (dusart_theta_mesh_generic_group623 S step @compose))))))) (compose (compose (compose (compose (compose (dusart_theta_mesh_generic_group624 S step @compose) (compose (dusart_theta_mesh_generic_group625 S step @compose) (dusart_theta_mesh_generic_group626 S step @compose))) (compose (dusart_theta_mesh_generic_group627 S step @compose) (compose (dusart_theta_mesh_generic_group628 S step @compose) (dusart_theta_mesh_generic_group629 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group630 S step @compose) (compose (dusart_theta_mesh_generic_group631 S step @compose) (dusart_theta_mesh_generic_group632 S step @compose))) (compose (dusart_theta_mesh_generic_group633 S step @compose) (compose (dusart_theta_mesh_generic_group634 S step @compose) (dusart_theta_mesh_generic_group635 S step @compose))))) (compose (compose (compose (dusart_theta_mesh_generic_group636 S step @compose) (compose (dusart_theta_mesh_generic_group637 S step @compose) (dusart_theta_mesh_generic_group638 S step @compose))) (compose (dusart_theta_mesh_generic_group639 S step @compose) (compose (dusart_theta_mesh_generic_group640 S step @compose) (dusart_theta_mesh_generic_group641 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group642 S step @compose) (compose (dusart_theta_mesh_generic_group643 S step @compose) (dusart_theta_mesh_generic_group644 S step @compose))) (compose (dusart_theta_mesh_generic_group645 S step @compose) (compose (dusart_theta_mesh_generic_group646 S step @compose) (dusart_theta_mesh_generic_group647 S step @compose)))))) (compose (compose (compose (compose (dusart_theta_mesh_generic_group648 S step @compose) (compose (dusart_theta_mesh_generic_group649 S step @compose) (dusart_theta_mesh_generic_group650 S step @compose))) (compose (dusart_theta_mesh_generic_group651 S step @compose) (compose (dusart_theta_mesh_generic_group652 S step @compose) (dusart_theta_mesh_generic_group653 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group654 S step @compose) (compose (dusart_theta_mesh_generic_group655 S step @compose) (dusart_theta_mesh_generic_group656 S step @compose))) (compose (dusart_theta_mesh_generic_group657 S step @compose) (compose (dusart_theta_mesh_generic_group658 S step @compose) (dusart_theta_mesh_generic_group659 S step @compose))))) (compose (compose (compose (dusart_theta_mesh_generic_group660 S step @compose) (compose (dusart_theta_mesh_generic_group661 S step @compose) (dusart_theta_mesh_generic_group662 S step @compose))) (compose (dusart_theta_mesh_generic_group663 S step @compose) (compose (dusart_theta_mesh_generic_group664 S step @compose) (dusart_theta_mesh_generic_group665 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group666 S step @compose) (compose (dusart_theta_mesh_generic_group667 S step @compose) (dusart_theta_mesh_generic_group668 S step @compose))) (compose (dusart_theta_mesh_generic_group669 S step @compose) (compose (dusart_theta_mesh_generic_group670 S step @compose) (dusart_theta_mesh_generic_group671 S step @compose))))))))
theorem interval6 : DusartMeshUpper.Literal.Spec 8052400384 9663013120 8052306946255057 9662936651771238 :=
 DusartProvedBridge.interpret interval6_generic
end DusartCompactIntervals


