-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans072
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans072
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:01:00.002659+00:00
-- url     : https://prove2.me/theorems/2de6b747-a244-45c5-bd37-7b03e0ab6e0e
-- title:
--   Endpoint22 Reach Plans072 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans072 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan6980`, `ThreeBoundEndpoint22Reachable.plan6981`, `ThreeBoundEndpoint22Reachable.plan6982`, `ThreeBoundEndpoint22Reachable.plan6983`, `ThreeBoundEndpoint22Reachable.plan6984`, `ThreeBoundEndpoint22Reachable.plan6985`, `ThreeBoundEndpoint22Reachable.plan6986`, `ThreeBoundEndpoint22Reachable.plan6987`, `ThreeBoundEndpoint22Reachable.plan6988`, `ThreeBoundEndpoint22Reachable.plan6989`, `ThreeBoundEndpoint22Reachable.plan6918`, `ThreeBoundEndpoint22Reachable.plan6990`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans072.lean, lines 1–206.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits011
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits012
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans057
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans058
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans059
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option Elab.async false
namespace ThreeBoundEndpoint22Reachable
open ThreeBoundRelaxedReachable ThreeBoundRelaxed
open ThreeBoundRelaxedCompiled (Int3)
def plan6913 : Plan := .step choices204 bits1500 plan5621

def plan6914 : Plan := .step choices204 bits1518 plan5632

def plan6915 : Plan := .step choices204 bits1522 plan5633

def plan6916 : Plan := .step choices204 bits1518 plan5634

def plan6917 : Plan := .step choices204 bits1524 plan5635

def plan6918 : Plan := .step choices204 bits1522 plan5636

def plan6919 : Plan := .step choices204 bits1518 plan5637

def plan6920 : Plan := .step choices204 bits1525 plan5638

def plan6921 : Plan := .step choices204 bits1524 plan5639

def plan6922 : Plan := .step choices204 bits1522 plan5640

def plan6923 : Plan := .step choices204 bits1518 plan5641

def plan6924 : Plan := .step choices204 bits1526 plan5642

def plan6925 : Plan := .step choices204 bits1525 plan5643

def plan6926 : Plan := .step choices204 bits1524 plan5644

def plan6927 : Plan := .step choices204 bits1522 plan5645

def plan6928 : Plan := .step choices204 bits1518 plan5646

def plan6929 : Plan := .step choices204 bits1514 plan5668

def plan6930 : Plan := .step choices204 bits1517 plan5669

def plan6931 : Plan := .step choices204 bits1514 plan5670

def plan6932 : Plan := .step choices204 bits1521 plan5671

def plan6933 : Plan := .step choices204 bits1517 plan5672

def plan6934 : Plan := .step choices204 bits1514 plan5673

def plan6935 : Plan := .step choices204 bits1523 plan5674

def plan6936 : Plan := .step choices204 bits1521 plan5675

def plan6937 : Plan := .step choices204 bits1517 plan5676

def plan6938 : Plan := .step choices204 bits1514 plan5677

def plan6939 : Plan := .step choices204 bits1511 plan5681

def plan6940 : Plan := .step choices204 bits1513 plan5682

def plan6941 : Plan := .step choices204 bits1511 plan5683

def plan6942 : Plan := .step choices204 bits1516 plan5684

def plan6943 : Plan := .step choices204 bits1513 plan5685

def plan6944 : Plan := .step choices204 bits1511 plan5686

def plan6945 : Plan := .step choices204 bits1510 plan5687

def plan6946 : Plan := .step choices204 bits1510 plan5688

def plan6947 : Plan := .step choices204 bits1511 plan5692

def plan6948 : Plan := .step choices204 bits1513 plan5693

def plan6949 : Plan := .step choices204 bits1511 plan5694

def plan6950 : Plan := .step choices204 bits1516 plan5695

def plan6951 : Plan := .step choices204 bits1513 plan5696

def plan6952 : Plan := .step choices204 bits1511 plan5697

def plan6953 : Plan := .step choices204 bits1510 plan5698

def plan6954 : Plan := .step choices204 bits1514 plan5720

def plan6955 : Plan := .step choices204 bits1517 plan5721

def plan6956 : Plan := .step choices204 bits1514 plan5722

def plan6957 : Plan := .step choices204 bits1521 plan5723

def plan6958 : Plan := .step choices204 bits1517 plan5724

def plan6959 : Plan := .step choices204 bits1514 plan5725

def plan6960 : Plan := .step choices204 bits1523 plan5726

def plan6961 : Plan := .step choices204 bits1521 plan5727

def plan6962 : Plan := .step choices204 bits1517 plan5728

def plan6963 : Plan := .step choices204 bits1514 plan5729

def plan6964 : Plan := .step choices204 bits1511 plan5733

def plan6965 : Plan := .step choices204 bits1513 plan5734

def plan6966 : Plan := .step choices204 bits1511 plan5735

def plan6967 : Plan := .step choices204 bits1516 plan5736

def plan6968 : Plan := .step choices204 bits1513 plan5737

def plan6969 : Plan := .step choices204 bits1511 plan5738

def plan6970 : Plan := .step choices204 bits1510 plan5739

def plan6971 : Plan := .step choices205 bits1534 plan5632

def plan6972 : Plan := .step choices205 bits1536 plan5633

def plan6973 : Plan := .step choices205 bits1534 plan5634

def plan6974 : Plan := .step choices205 bits1538 plan5635

def plan6975 : Plan := .step choices205 bits1536 plan5636

def plan6976 : Plan := .step choices205 bits1534 plan5637

def plan6977 : Plan := .step choices205 bits1539 plan5638

def plan6978 : Plan := .step choices205 bits1538 plan5639

def plan6979 : Plan := .step choices205 bits1536 plan5640

def plan6980 : Plan := .step choices205 bits1534 plan5641

def plan6981 : Plan := .step choices205 bits1540 plan5642

def plan6982 : Plan := .step choices205 bits1539 plan5643

def plan6983 : Plan := .step choices205 bits1538 plan5644

def plan6984 : Plan := .step choices205 bits1536 plan5645

def plan6985 : Plan := .step choices205 bits1534 plan5646

def plan6986 : Plan := .step choices206 bits1480 plan5554

def plan6987 : Plan := .step choices206 bits1481 plan5555

def plan6988 : Plan := .step choices206 bits1484 plan5556

def plan6989 : Plan := .step choices206 bits1481 plan5557

def plan6990 : Plan := .step choices206 bits1487 plan5558

def plan6991 : Plan := .step choices206 bits1480 plan5559

def plan6992 : Plan := .step choices206 bits1484 plan5560

def plan6993 : Plan := .step choices206 bits1481 plan5561

def plan6994 : Plan := .step choices206 bits1494 plan5562

def plan6995 : Plan := .step choices206 bits1498 plan5563

def plan6996 : Plan := .step choices206 bits1494 plan5564

def plan6997 : Plan := .step choices206 bits1501 plan5565

def plan6998 : Plan := .step choices206 bits1498 plan5566

def plan6999 : Plan := .step choices206 bits1494 plan5567

def plan7000 : Plan := .step choices206 bits1504 plan5568

def plan7001 : Plan := .step choices206 bits1501 plan5569

def plan7002 : Plan := .step choices206 bits1498 plan5570

def plan7003 : Plan := .step choices206 bits1494 plan5571

def plan7004 : Plan := .step choices206 bits1493 plan5572

def plan7005 : Plan := .step choices206 bits1497 plan5573

def plan7006 : Plan := .step choices206 bits1493 plan5574

def plan7007 : Plan := .step choices206 bits1493 plan5602

def plan7008 : Plan := .step choices206 bits1497 plan5603

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


