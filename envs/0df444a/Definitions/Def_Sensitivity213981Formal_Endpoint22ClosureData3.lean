-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ClosureData3
-- name    : Sensitivity213981Formal_Endpoint22ClosureData3
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T21:13:04.90878+00:00
-- url     : https://prove2.me/theorems/778d223e-86f3-443c-8983-954949dc3eb4
-- title:
--   Endpoint22 Closure Data3 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Closure Data3 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundMinmaxNumeric.Endpoint22.outputIndex3`, `ThreeBoundMinmaxNumeric.Endpoint22.nodeCount3`, `ThreeBoundMinmaxNumeric.Endpoint22.newNodes3`, `ThreeBoundMinmaxNumeric.Endpoint22.nodes3`, `ThreeBoundMinmaxNumeric.Endpoint22.outputPointers3`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ClosureData3.lean, lines 1–503.

import Definitions.Def_Sensitivity213981Formal_ClosureCertificate
import Definitions.Def_Sensitivity213981Formal_Endpoint22ClosureCoordinates
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
namespace ThreeBoundMinmaxNumeric.Endpoint22
open ThreeBoundNumeric ThreeBoundFullProfile ClosureCertificate
def newNodes3:Table (Node 22):=
(.branch 2766
(.branch 2752
(.branch 2745
(.branch 2742
(.branch 2740
(.leaf ⟨(.d 6 6 10),9140870028015299476665,.step (.dUp 6 6 10 (by decide) (by decide)) 1431 1431⟩)
(.branch 2741
(.leaf ⟨(.d 6 6 11),9140870028015299476665,.step (.dUp 6 6 11 (by decide) (by decide)) 2739 2739⟩)
(.leaf ⟨(.d 6 6 14),9140870028015299476665,.step (.dUp 6 6 14 (by decide) (by decide)) 1435 1435⟩)))
(.branch 2743
(.leaf ⟨(.d 5 6 10),9140870028015299476665,.step (.dDown 5 6 10 (by decide) (by decide)) 2739 2739⟩)
(.branch 2744
(.leaf ⟨(.d 5 6 11),9140870028015299476665,.step (.dDown 5 6 11 (by decide) (by decide)) 2740 2740⟩)
(.leaf ⟨(.d 5 6 14),9140870028015299476665,.step (.dDown 5 6 14 (by decide) (by decide)) 2741 2741⟩))))
(.branch 2748
(.branch 2746
(.leaf ⟨(.d 7 7 10),9614543534837734867175,.step (.dUp 7 7 10 (by decide) (by decide)) 1543 1543⟩)
(.branch 2747
(.leaf ⟨(.d 7 7 11),9614543534837734867175,.step (.dUp 7 7 11 (by decide) (by decide)) 2745 2745⟩)
(.leaf ⟨(.d 7 7 14),9614543534837734867175,.step (.dUp 7 7 14 (by decide) (by decide)) 1547 1547⟩)))
(.branch 2750
(.branch 2749
(.leaf ⟨(.d 6 7 10),8689973895789649540190,.step (.dUp 6 7 10 (by decide) (by decide)) 1529 1529⟩)
(.leaf ⟨(.d 6 7 11),8689973895789649540190,.step (.dUp 6 7 11 (by decide) (by decide)) 2748 2748⟩))
(.branch 2751
(.leaf ⟨(.d 6 7 14),8689973895789649540190,.step (.dUp 6 7 14 (by decide) (by decide)) 1533 1533⟩)
(.leaf ⟨(.p 8 10),3014369446584378841,.step (.pTarget 8 10 (by decide)) 877 877⟩)))))
(.branch 2759
(.branch 2755
(.branch 2753
(.leaf ⟨(.p 8 11),3014369446584378841,.step (.pTarget 8 11 (by decide)) 2751 2751⟩)
(.branch 2754
(.leaf ⟨(.p 8 14),209814832311730248,.step (.pTarget 8 14 (by decide)) 881 881⟩)
(.leaf ⟨(.d 8 8 10),28456869294326111779175,.step (.dUp 8 8 10 (by decide) (by decide)) 1660 1660⟩)))
(.branch 2757
(.branch 2756
(.leaf ⟨(.d 8 8 11),28456869294326111779175,.step (.dUp 8 8 11 (by decide) (by decide)) 2754 2754⟩)
(.leaf ⟨(.d 8 8 14),28456869294326111779175,.step (.dUp 8 8 14 (by decide) (by decide)) 1664 1664⟩))
(.branch 2758
(.leaf ⟨(.d 7 8 10),114480224849691296121,.step (.dFromMP 7 8 10 (by decide) (by decide)) 549 2751⟩)
(.leaf ⟨(.d 7 8 11),114480224849691296121,.step (.dFromMP 7 8 11 (by decide) (by decide)) 549 2752⟩))))
(.branch 2762
(.branch 2760
(.leaf ⟨(.d 7 8 14),111675670235418647528,.step (.dFromMP 7 8 14 (by decide) (by decide)) 549 2753⟩)
(.branch 2761
(.leaf ⟨(.d 6 8 10),114338480532833635573,.step (.dUp 6 8 10 (by decide) (by decide)) 1634 1634⟩)
(.leaf ⟨(.d 6 8 11),114338480532833635573,.step (.dUp 6 8 11 (by decide) (by decide)) 2760 2760⟩)))
(.branch 2764
(.branch 2763
(.leaf ⟨(.d 6 8 14),111465855403106917280,.step (.dUp 6 8 14 (by decide) (by decide)) 1638 1638⟩)
(.leaf ⟨(.d 5 8 10),110762670461202503321,.step (.dFromMP 5 8 10 (by decide) (by decide)) 547 2751⟩))
(.branch 2765
(.leaf ⟨(.d 5 8 11),110762670461202503321,.step (.dFromMP 5 8 11 (by decide) (by decide)) 547 2752⟩)
(.leaf ⟨(.d 5 8 14),107958115846929854728,.step (.dFromMP 5 8 14 (by decide) (by decide)) 547 2753⟩))))))
(.branch 2779
(.branch 2772
(.branch 2769
(.branch 2767
(.leaf ⟨(.d 4 8 10),7097160839641789601,.step (.dFromMP 4 8 10 (by decide) (by decide)) 546 2751⟩)
(.branch 2768
(.leaf ⟨(.d 4 8 11),7097160839641789601,.step (.dFromMP 4 8 11 (by decide) (by decide)) 546 2752⟩)
(.leaf ⟨(.d 4 8 14),4292606225369141008,.step (.dFromMP 4 8 14 (by decide) (by decide)) 546 2753⟩)))
(.branch 2770
(.leaf ⟨(.d 3 8 10),7097160839641789601,.step (.dFromMP 3 8 10 (by decide) (by decide)) 545 2751⟩)
(.branch 2771
(.leaf ⟨(.d 3 8 11),7097160839641789601,.step (.dFromMP 3 8 11 (by decide) (by decide)) 545 2752⟩)
(.leaf ⟨(.d 3 8 14),4292606225369141008,.step (.dFromMP 3 8 14 (by decide) (by decide)) 545 2753⟩))))
(.branch 2775
(.branch 2773
(.leaf ⟨(.d 2 8 10),7097160839641789601,.step (.dFromMP 2 8 10 (by decide) (by decide)) 544 2751⟩)
(.branch 2774
(.leaf ⟨(.d 2 8 11),7097160839641789601,.step (.dFromMP 2 8 11 (by decide) (by decide)) 544 2752⟩)
(.leaf ⟨(.d 2 8 14),4292606225369141008,.step (.dFromMP 2 8 14 (by decide) (by decide)) 544 2753⟩)))
(.branch 2777
(.branch 2776
(.leaf ⟨(.d 1 8 10),7097160839641789601,.step (.dFromMP 1 8 10 (by decide) (by decide)) 543 2751⟩)
(.leaf ⟨(.d 1 8 11),7097160839641789601,.step (.dFromMP 1 8 11 (by decide) (by decide)) 543 2752⟩))
(.branch 2778
(.leaf ⟨(.d 1 8 14),4292606225369141008,.step (.dFromMP 1 8 14 (by decide) (by decide)) 543 2753⟩)
(.leaf ⟨(.d 0 8 10),7097160839641789601,.step (.dFromMP 0 8 10 (by decide) (by decide)) 542 2751⟩)))))
(.branch 2786
(.branch 2782
(.branch 2780
(.leaf ⟨(.d 0 8 11),7097160839641789601,.step (.dFromMP 0 8 11 (by decide) (by decide)) 542 2752⟩)
(.branch 2781
(.leaf ⟨(.d 0 8 14),4292606225369141008,.step (.dFromMP 0 8 14 (by decide) (by decide)) 542 2753⟩)
(.leaf ⟨(.d 9 9 14),28551364319545893282505,.step (.dUp 9 9 14 (by decide) (by decide)) 1784 1784⟩)))
(.branch 2784
(.branch 2783
(.leaf ⟨(.d 8 9 14),28400988712912282824405,.step (.dUp 8 9 14 (by decide) (by decide)) 1772 1772⟩)
(.leaf ⟨(.d 6 9 14),111465855403106917280,.step (.dUp 6 9 14 (by decide) (by decide)) 1748 1748⟩))
(.branch 2785
(.leaf ⟨(.d 10 10 14),29185874261655262440285,.step (.dUp 10 10 14 (by decide) (by decide)) 1905 1905⟩)
(.leaf ⟨(.d 9 10 14),27600569824435877094185,.step (.dUp 9 10 14 (by decide) (by decide)) 1894 1894⟩))))
(.branch 2789
(.branch 2787
(.leaf ⟨(.d 8 10 14),27525382021119071865135,.step (.dUp 8 10 14 (by decide) (by decide)) 1883 1883⟩)
(.branch 2788
(.leaf ⟨(.d 11 11 14),54487385751175935773185,.step (.dUp 11 11 14 (by decide) (by decide)) 2025 2025⟩)
(.leaf ⟨(.d 10 11 14),29185874261655262440285,.step (.dUp 10 11 14 (by decide) (by decide)) 2015 2015⟩)))
(.branch 2791
(.branch 2790
(.leaf ⟨(.d 9 11 14),27600569824435877094185,.step (.dUp 9 11 14 (by decide) (by decide)) 2005 2005⟩)
(.leaf ⟨(.d 8 11 14),27525382021119071865135,.step (.dUp 8 11 14 (by decide) (by decide)) 1995 1995⟩))
(.branch 2792
(.leaf ⟨(.d 9 12 14),26649775329325860905865,.step (.dUp 9 12 14 (by decide) (by decide)) 2115 2115⟩)
(.leaf ⟨(.d 8 12 14),26649775329325860905865,.step (.dDown 8 12 14 (by decide) (by decide)) 2791 2791⟩)))))))
def nodes3 (k:ℕ):Node 22:=
  if k< 2739 then ⟨coordOfIndex k,rawProfile3 (coordOfIndex k),.input⟩
  else newNodes3.get k
def outputPointers3:PointerTable:=
(.branch 1369
(.branch 684
.identity
(.branch 1026
(.branch 855
.identity
(.branch 940
(.branch 897
(.branch 876
.identity
(.branch 886
(.branch 881
(.branch 878
.identity
(.branch 879
(.fixed 2751)
(.branch 880
(.fixed 2752)
.identity)))
(.branch 883
(.branch 882
.identity
(.fixed 2753))
.identity))
.identity))
.identity)
.identity))
.identity))
(.branch 2054
(.branch 1711
(.branch 1540
(.branch 1454
(.branch 1411
.identity
(.branch 1432
(.branch 1421
(.branch 1416
.identity
(.branch 1418
(.branch 1417
.identity
(.fixed 2742))
(.branch 1419
(.fixed 2743)
.identity)))
(.branch 1426
(.branch 1423
(.branch 1422
(.fixed 2744)
.identity)
.identity)
.identity))
(.branch 1443
(.branch 1437
(.branch 1434
(.branch 1433
(.fixed 2739)
(.fixed 2740))
(.branch 1435
.identity
(.branch 1436
.identity
(.fixed 2741))))
.identity)
.identity)))
(.branch 1497
.identity
(.branch 1518
.identity
(.branch 1529
.identity
(.branch 1534
(.branch 1531
(.branch 1530
.identity
(.fixed 2748))
(.branch 1532
(.fixed 2749)
.identity))
(.branch 1537
(.branch 1535
(.fixed 2750)
.identity)
.identity))))))
(.branch 1625
(.branch 1582
(.branch 1561
(.branch 1550
(.branch 1545
(.branch 1542
.identity
(.branch 1543
.identity
(.branch 1544
.identity
(.fixed 2745))))
(.branch 1547
(.branch 1546
(.fixed 2746)
.identity)
(.branch 1548
.identity
(.branch 1549
(.fixed 2747)
.identity))))
(.branch 1555
.identity
(.branch 1558
(.branch 1556
.identity
(.branch 1557
.identity
(.fixed 2778)))
(.branch 1559
(.fixed 2779)
.identity))))
(.branch 1571
(.branch 1566
(.branch 1563
(.branch 1562
(.fixed 2780)
.identity)
.identity)
(.branch 1568
.identity
(.branch 1569
.identity
(.branch 1570
.identity
(.fixed 2775)))))
(.branch 1576
(.branch 1573
(.branch 1572
(.fixed 2776)
.identity)
(.branch 1574
.identity
(.branch 1575
(.fixed 2777)
.identity)))
.identity)))
(.branch 1603
(.branch 1592
(.branch 1587
(.branch 1584
(.branch 1583
.identity
(.fixed 2772))
(.branch 1585
(.fixed 2773)
.identity))
(.branch 1589
(.branch 1588
(.fixed 2774)
.identity)
.identity))
(.branch 1597
(.branch 1594
.identity
(.branch 1595
.identity
(.branch 1596
.identity
(.fixed 2769))))
(.branch 1600
(.branch 1598
(.fixed 2770)
.identity)
(.branch 1601
(.fixed 2771)
.identity))))
(.branch 1614
(.branch 1608
.identity
(.branch 1611
(.branch 1609
.identity
(.branch 1610
(.fixed 2766)
(.fixed 2767)))
(.branch 1612
.identity
(.branch 1613
.identity
(.fixed 2768)))))
(.branch 1619
.identity
(.branch 1622
.identity
(.branch 1623
(.fixed 2763)
(.branch 1624
(.fixed 2764)
.identity)))))))
(.branch 1668
(.branch 1646
(.branch 1635
(.branch 1630
(.branch 1627
(.branch 1626
.identity
(.fixed 2765))
.identity)
.identity)
(.branch 1640
(.branch 1637
(.branch 1636
(.fixed 2760)
(.fixed 2761))
(.branch 1638
.identity
(.branch 1639
.identity
(.fixed 2762))))
.identity))
(.branch 1657
(.branch 1651
(.branch 1648
.identity
(.branch 1649
(.fixed 2757)
(.branch 1650
(.fixed 2758)
.identity)))
(.branch 1654
(.branch 1652
.identity
(.branch 1653
(.fixed 2759)
.identity))
.identity))
(.branch 1662
(.branch 1659
.identity
(.branch 1660
.identity
(.branch 1661
.identity
(.fixed 2754))))
(.branch 1665
(.branch 1663
(.fixed 2755)
.identity)
(.branch 1666
(.fixed 2756)
.identity)))))
.identity)))
(.branch 1882
(.branch 1796
(.branch 1753
(.branch 1732
.identity
(.branch 1742
.identity
(.branch 1747
.identity
(.branch 1750
(.branch 1748
.identity
(.branch 1749
.identity
(.fixed 2783)))
.identity))))
(.branch 1774
(.branch 1763
.identity
(.branch 1768
.identity
(.branch 1771
.identity
(.branch 1772
.identity
(.branch 1773
.identity
(.fixed 2782))))))
(.branch 1785
.identity
(.branch 1790
(.branch 1787
(.branch 1786
(.fixed 2781)
.identity)
.identity)
.identity))))
.identity)
(.branch 1968
(.branch 1925
(.branch 1903
(.branch 1892
(.branch 1887
(.branch 1884
.identity
(.branch 1885
(.fixed 2786)
.identity))
.identity)
(.branch 1897
(.branch 1894
.identity
(.branch 1895
.identity
(.branch 1896
(.fixed 2785)
.identity)))
.identity))
(.branch 1914
(.branch 1908
(.branch 1905
.identity
(.branch 1906
.identity
(.branch 1907
(.fixed 2784)
.identity)))
.identity)
.identity))
.identity)
(.branch 2011
(.branch 1989
.identity
(.branch 2000
(.branch 1994
.identity
(.branch 1997
(.branch 1995
.identity
(.branch 1996
.identity
(.fixed 2790)))
.identity))
(.branch 2005
.identity
(.branch 2008
(.branch 2006
.identity
(.branch 2007
(.fixed 2789)
.identity))
.identity))))
(.branch 2032
(.branch 2021
(.branch 2016
.identity
(.branch 2018
(.branch 2017
(.fixed 2788)
.identity)
.identity))
(.branch 2026
.identity
(.branch 2029
(.branch 2027
(.fixed 2787)
.identity)
.identity)))
.identity)))))
(.branch 2396
(.branch 2225
(.branch 2139
(.branch 2096
.identity
(.branch 2117
(.branch 2106
.identity
(.branch 2111
(.branch 2108
(.branch 2107
.identity
(.fixed 2792))
.identity)
(.branch 2114
.identity
(.branch 2115
.identity
(.branch 2116
.identity
(.fixed 2791))))))
.identity))
.identity)
.identity)
.identity)))
def outputIndex3 (c:Coord 22):ℕ:=outputPointers3.get (flatIndex c)
def nodeCount3:ℕ:=2793
end ThreeBoundMinmaxNumeric.Endpoint22

end
end Sensitivity213981Formal


