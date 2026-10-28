-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks143
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks143
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:30:43.768251+00:00
-- url     : https://prove2.me/theorems/dbfae4d2-08ea-411b-8c7b-511700d5f356
-- title:
--   Endpoint22 Reach Checks143 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks143 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_1528root`, `ThreeBoundEndpoint22Reachable.t6_1528jobs0`, `ThreeBoundEndpoint22Reachable.t6_1528jobs`, `ThreeBoundEndpoint22Reachable.t6_1529root`, `ThreeBoundEndpoint22Reachable.t6_1529jobs0`, `ThreeBoundEndpoint22Reachable.t6_1529jobs`, `ThreeBoundEndpoint22Reachable.t6_1530root`, `ThreeBoundEndpoint22Reachable.t6_1530jobs0`, `ThreeBoundEndpoint22Reachable.t6_1530jobs1`, `ThreeBoundEndpoint22Reachable.t6_1530jobs`, `ThreeBoundEndpoint22Reachable.t6_1531root`, `ThreeBoundEndpoint22Reachable.t6_1531jobs0`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks143.lean, lines 1–753.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans066
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans069
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans074
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans079
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans082
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
open ThreeBoundEndpoint22Packed (tree)

def t6_1516root : Job := ⟨plan7631,[],none,⟨15,10,0⟩⟩
def t6_1516jobs0 : List Job := [⟨plan7631,[],none,⟨15,10,0⟩⟩]

def t6_1516jobs : List Job := t6_1516jobs0




def t6_1517root : Job := ⟨plan6428,[],none,⟨15,1,0⟩⟩
def t6_1517jobs0 : List Job := [⟨plan6428,[],none,⟨15,1,0⟩⟩]

def t6_1517jobs : List Job := t6_1517jobs0




def t6_1518root : Job := ⟨plan6677,[],none,⟨15,3,0⟩⟩
def t6_1518jobs0 : List Job := [⟨plan6677,[],none,⟨15,3,0⟩⟩]

def t6_1518jobs : List Job := t6_1518jobs0




def t6_1519root : Job := ⟨plan6678,[],none,⟨15,3,0⟩⟩
def t6_1519jobs0 : List Job := [⟨plan6678,[],none,⟨15,3,0⟩⟩]

def t6_1519jobs : List Job := t6_1519jobs0




def t6_1520root : Job := ⟨plan6679,[],none,⟨15,3,0⟩⟩
def t6_1520jobs0 : List Job := [⟨plan6679,[],none,⟨15,3,0⟩⟩]

def t6_1520jobs : List Job := t6_1520jobs0




def t6_1521root : Job := ⟨plan7108,[],none,⟨15,6,0⟩⟩
def t6_1521jobs0 : List Job := [⟨plan7108,[],none,⟨15,6,0⟩⟩]

def t6_1521jobs : List Job := t6_1521jobs0




def t6_1522root : Job := ⟨plan7109,[],none,⟨15,6,0⟩⟩
def t6_1522jobs0 : List Job := [⟨plan5663,[⟨8,0,3⟩],(some ⟨8,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5663,[⟨8,1,2⟩],(some ⟨8,1,2⟩),⟨14,4,(-1)⟩⟩]

def t6_1522jobs1 : List Job := [⟨plan5663,[⟨8,1,3⟩],(some ⟨8,1,3⟩),⟨14,3,(-2)⟩⟩]

def t6_1522jobs : List Job := t6_1522jobs0++t6_1522jobs1




def t6_1523root : Job := ⟨plan7110,[],none,⟨15,6,0⟩⟩
def t6_1523jobs0 : List Job := [⟨plan7110,[],none,⟨15,6,0⟩⟩]

def t6_1523jobs : List Job := t6_1523jobs0




def t6_1524root : Job := ⟨plan7111,[],none,⟨15,6,0⟩⟩
def t6_1524jobs0 : List Job := [⟨plan5665,[⟨8,0,3⟩],(some ⟨8,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5665,[⟨8,1,2⟩],(some ⟨8,1,2⟩),⟨14,4,(-1)⟩⟩]

def t6_1524jobs1 : List Job := [⟨plan5665,[⟨8,1,3⟩],(some ⟨8,1,3⟩),⟨14,3,(-2)⟩⟩]

def t6_1524jobs : List Job := t6_1524jobs0++t6_1524jobs1




def t6_1525root : Job := ⟨plan7112,[],none,⟨15,6,0⟩⟩
def t6_1525jobs0 : List Job := [⟨plan5666,[⟨8,0,3⟩],(some ⟨8,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5666,[⟨8,1,2⟩],(some ⟨8,1,2⟩),⟨14,4,(-1)⟩⟩]

def t6_1525jobs1 : List Job := [⟨plan5666,[⟨8,1,3⟩],(some ⟨8,1,3⟩),⟨14,3,(-2)⟩⟩]

def t6_1525jobs : List Job := t6_1525jobs0++t6_1525jobs1




def t6_1526root : Job := ⟨plan7113,[],none,⟨15,6,0⟩⟩
def t6_1526jobs0 : List Job := [⟨plan7113,[],none,⟨15,6,0⟩⟩]

def t6_1526jobs : List Job := t6_1526jobs0




def t6_1527root : Job := ⟨plan7632,[],none,⟨15,10,0⟩⟩
def t6_1527jobs0 : List Job := [⟨plan7632,[],none,⟨15,10,0⟩⟩]

def t6_1527jobs : List Job := t6_1527jobs0




def t6_1528root : Job := ⟨plan7633,[],none,⟨15,10,0⟩⟩
def t6_1528jobs0 : List Job := [⟨plan7633,[],none,⟨15,10,0⟩⟩]

def t6_1528jobs : List Job := t6_1528jobs0




def t6_1529root : Job := ⟨plan7634,[],none,⟨15,10,0⟩⟩
def t6_1529jobs0 : List Job := [⟨plan7634,[],none,⟨15,10,0⟩⟩]

def t6_1529jobs : List Job := t6_1529jobs0




def t6_1530root : Job := ⟨plan7635,[],none,⟨15,10,0⟩⟩
def t6_1530jobs0 : List Job := [⟨plan5817,[⟨8,0,4⟩],(some ⟨8,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5817,[⟨8,1,3⟩],(some ⟨8,1,3⟩),⟨14,7,(-2)⟩⟩]

def t6_1530jobs1 : List Job := [⟨plan5817,[⟨8,1,4⟩],(some ⟨8,1,4⟩),⟨14,6,(-3)⟩⟩]

def t6_1530jobs : List Job := t6_1530jobs0++t6_1530jobs1




def t6_1531root : Job := ⟨plan7636,[],none,⟨15,10,0⟩⟩
def t6_1531jobs0 : List Job := [⟨plan7636,[],none,⟨15,10,0⟩⟩]

def t6_1531jobs : List Job := t6_1531jobs0




def t6_1532root : Job := ⟨plan7637,[],none,⟨15,10,0⟩⟩
def t6_1532jobs0 : List Job := [⟨plan7637,[],none,⟨15,10,0⟩⟩]

def t6_1532jobs : List Job := t6_1532jobs0




def t6_1533root : Job := ⟨plan7638,[],none,⟨15,10,0⟩⟩
def t6_1533jobs0 : List Job := [⟨plan5820,[⟨8,0,4⟩],(some ⟨8,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5820,[⟨8,1,3⟩],(some ⟨8,1,3⟩),⟨14,7,(-2)⟩⟩]

def t6_1533jobs1 : List Job := [⟨plan5820,[⟨8,1,4⟩],(some ⟨8,1,4⟩),⟨14,6,(-3)⟩⟩]

def t6_1533jobs : List Job := t6_1533jobs0++t6_1533jobs1




def t6_1534root : Job := ⟨plan7639,[],none,⟨15,10,0⟩⟩
def t6_1534jobs0 : List Job := [⟨plan5821,[⟨8,0,4⟩],(some ⟨8,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5821,[⟨8,1,3⟩],(some ⟨8,1,3⟩),⟨14,7,(-2)⟩⟩]

def t6_1534jobs1 : List Job := [⟨plan5821,[⟨8,1,4⟩],(some ⟨8,1,4⟩),⟨14,6,(-3)⟩⟩]

def t6_1534jobs : List Job := t6_1534jobs0++t6_1534jobs1




def t6_1535root : Job := ⟨plan7640,[],none,⟨15,10,0⟩⟩
def t6_1535jobs0 : List Job := [⟨plan7640,[],none,⟨15,10,0⟩⟩]

def t6_1535jobs : List Job := t6_1535jobs0




def t6_1536root : Job := ⟨plan7641,[],none,⟨15,10,0⟩⟩
def t6_1536jobs0 : List Job := [⟨plan7641,[],none,⟨15,10,0⟩⟩]

def t6_1536jobs : List Job := t6_1536jobs0




def t6_1537root : Job := ⟨plan7114,[],none,⟨15,6,0⟩⟩
def t6_1537jobs0 : List Job := [⟨plan7114,[],none,⟨15,6,0⟩⟩]

def t6_1537jobs : List Job := t6_1537jobs0




def t6_1538root : Job := ⟨plan7642,[],none,⟨15,10,0⟩⟩
def t6_1538jobs0 : List Job := [⟨plan7642,[],none,⟨15,10,0⟩⟩]

def t6_1538jobs : List Job := t6_1538jobs0




def t6_1539root : Job := ⟨plan7643,[],none,⟨15,10,0⟩⟩
def t6_1539jobs0 : List Job := [⟨plan7643,[],none,⟨15,10,0⟩⟩]

def t6_1539jobs : List Job := t6_1539jobs0




def t6_1540root : Job := ⟨plan7644,[],none,⟨15,10,0⟩⟩
def t6_1540jobs0 : List Job := [⟨plan7644,[],none,⟨15,10,0⟩⟩]

def t6_1540jobs : List Job := t6_1540jobs0




def t6_1541root : Job := ⟨plan7927,[],none,⟨15,15,0⟩⟩
def t6_1541jobs0 : List Job := [⟨plan7927,[],none,⟨15,15,0⟩⟩]

def t6_1541jobs : List Job := t6_1541jobs0




def t6_1542root : Job := ⟨plan7928,[],none,⟨15,15,0⟩⟩
def t6_1542jobs0 : List Job := [⟨plan7928,[],none,⟨15,15,0⟩⟩]

def t6_1542jobs : List Job := t6_1542jobs0




def t6_1543root : Job := ⟨plan7929,[],none,⟨15,15,0⟩⟩
def t6_1543jobs0 : List Job := [⟨plan7929,[],none,⟨15,15,0⟩⟩]

def t6_1543jobs : List Job := t6_1543jobs0




def t6_1544root : Job := ⟨plan7930,[],none,⟨15,15,0⟩⟩
def t6_1544jobs0 : List Job := [⟨plan7930,[],none,⟨15,15,0⟩⟩]

def t6_1544jobs : List Job := t6_1544jobs0




def t6_1545root : Job := ⟨plan7931,[],none,⟨15,15,0⟩⟩
def t6_1545jobs0 : List Job := [⟨plan7931,[],none,⟨15,15,0⟩⟩]

def t6_1545jobs : List Job := t6_1545jobs0




def t6_1546root : Job := ⟨plan7932,[],none,⟨15,15,0⟩⟩
def t6_1546jobs0 : List Job := [⟨plan7932,[],none,⟨15,15,0⟩⟩]

def t6_1546jobs : List Job := t6_1546jobs0




def t6_1547root : Job := ⟨plan7933,[],none,⟨15,15,0⟩⟩
def t6_1547jobs0 : List Job := [⟨plan7933,[],none,⟨15,15,0⟩⟩]

def t6_1547jobs : List Job := t6_1547jobs0




def t6_1548root : Job := ⟨plan7934,[],none,⟨15,15,0⟩⟩
def t6_1548jobs0 : List Job := [⟨plan7934,[],none,⟨15,15,0⟩⟩]

def t6_1548jobs : List Job := t6_1548jobs0




def t6_1549root : Job := ⟨plan7935,[],none,⟨15,15,0⟩⟩
def t6_1549jobs0 : List Job := [⟨plan7935,[],none,⟨15,15,0⟩⟩]

def t6_1549jobs : List Job := t6_1549jobs0




def t6_1550root : Job := ⟨plan7936,[],none,⟨15,15,0⟩⟩
def t6_1550jobs0 : List Job := [⟨plan7936,[],none,⟨15,15,0⟩⟩]

def t6_1550jobs : List Job := t6_1550jobs0




def t6_1551root : Job := ⟨plan7937,[],none,⟨15,15,0⟩⟩
def t6_1551jobs0 : List Job := [⟨plan7937,[],none,⟨15,15,0⟩⟩]

def t6_1551jobs : List Job := t6_1551jobs0




def t6_1552root : Job := ⟨plan7938,[],none,⟨15,15,0⟩⟩
def t6_1552jobs0 : List Job := [⟨plan7938,[],none,⟨15,15,0⟩⟩]

def t6_1552jobs : List Job := t6_1552jobs0




def t6_1553root : Job := ⟨plan7939,[],none,⟨15,15,0⟩⟩
def t6_1553jobs0 : List Job := [⟨plan7939,[],none,⟨15,15,0⟩⟩]

def t6_1553jobs : List Job := t6_1553jobs0




def t6_1554root : Job := ⟨plan7940,[],none,⟨15,15,0⟩⟩
def t6_1554jobs0 : List Job := [⟨plan7940,[],none,⟨15,15,0⟩⟩]

def t6_1554jobs : List Job := t6_1554jobs0




def t6_1555root : Job := ⟨plan7941,[],none,⟨15,15,0⟩⟩
def t6_1555jobs0 : List Job := [⟨plan7941,[],none,⟨15,15,0⟩⟩]

def t6_1555jobs : List Job := t6_1555jobs0




def t6_1556root : Job := ⟨plan7942,[],none,⟨15,15,0⟩⟩
def t6_1556jobs0 : List Job := [⟨plan7942,[],none,⟨15,15,0⟩⟩]

def t6_1556jobs : List Job := t6_1556jobs0




def t6_1557root : Job := ⟨plan7943,[],none,⟨15,15,0⟩⟩
def t6_1557jobs0 : List Job := [⟨plan7943,[],none,⟨15,15,0⟩⟩]

def t6_1557jobs : List Job := t6_1557jobs0




def t6_1558root : Job := ⟨plan7944,[],none,⟨15,15,0⟩⟩
def t6_1558jobs0 : List Job := [⟨plan7944,[],none,⟨15,15,0⟩⟩]

def t6_1558jobs : List Job := t6_1558jobs0




def t6_1559root : Job := ⟨plan7945,[],none,⟨15,15,0⟩⟩
def t6_1559jobs0 : List Job := [⟨plan7945,[],none,⟨15,15,0⟩⟩]

def t6_1559jobs : List Job := t6_1559jobs0




def t6_1560root : Job := ⟨plan7115,[],none,⟨15,6,0⟩⟩
def t6_1560jobs0 : List Job := [⟨plan7115,[],none,⟨15,6,0⟩⟩]

def t6_1560jobs : List Job := t6_1560jobs0




def t6_1561root : Job := ⟨plan7645,[],none,⟨15,10,0⟩⟩
def t6_1561jobs0 : List Job := [⟨plan7645,[],none,⟨15,10,0⟩⟩]

def t6_1561jobs : List Job := t6_1561jobs0




def t6_1562root : Job := ⟨plan7646,[],none,⟨15,10,0⟩⟩
def t6_1562jobs0 : List Job := [⟨plan7646,[],none,⟨15,10,0⟩⟩]

def t6_1562jobs : List Job := t6_1562jobs0




def t6_1563root : Job := ⟨plan7647,[],none,⟨15,10,0⟩⟩
def t6_1563jobs0 : List Job := [⟨plan7647,[],none,⟨15,10,0⟩⟩]

def t6_1563jobs : List Job := t6_1563jobs0




def t6_1564root : Job := ⟨plan7946,[],none,⟨15,15,0⟩⟩
def t6_1564jobs0 : List Job := [⟨plan7946,[],none,⟨15,15,0⟩⟩]

def t6_1564jobs : List Job := t6_1564jobs0




def t6_1565root : Job := ⟨plan7947,[],none,⟨15,15,0⟩⟩
def t6_1565jobs0 : List Job := [⟨plan7947,[],none,⟨15,15,0⟩⟩]

def t6_1565jobs : List Job := t6_1565jobs0




def t6_1566root : Job := ⟨plan7948,[],none,⟨15,15,0⟩⟩
def t6_1566jobs0 : List Job := [⟨plan7948,[],none,⟨15,15,0⟩⟩]

def t6_1566jobs : List Job := t6_1566jobs0




def t6_1567root : Job := ⟨plan7949,[],none,⟨15,15,0⟩⟩
def t6_1567jobs0 : List Job := [⟨plan7949,[],none,⟨15,15,0⟩⟩]

def t6_1567jobs : List Job := t6_1567jobs0




def t6_1568root : Job := ⟨plan7950,[],none,⟨15,15,0⟩⟩
def t6_1568jobs0 : List Job := [⟨plan7950,[],none,⟨15,15,0⟩⟩]

def t6_1568jobs : List Job := t6_1568jobs0




def t6_1569root : Job := ⟨plan7951,[],none,⟨15,15,0⟩⟩
def t6_1569jobs0 : List Job := [⟨plan7951,[],none,⟨15,15,0⟩⟩]

def t6_1569jobs : List Job := t6_1569jobs0




def t6_1570root : Job := ⟨plan7952,[],none,⟨15,15,0⟩⟩
def t6_1570jobs0 : List Job := [⟨plan7952,[],none,⟨15,15,0⟩⟩]

def t6_1570jobs : List Job := t6_1570jobs0




def t6_1571root : Job := ⟨plan7953,[],none,⟨15,15,0⟩⟩
def t6_1571jobs0 : List Job := [⟨plan7953,[],none,⟨15,15,0⟩⟩]

def t6_1571jobs : List Job := t6_1571jobs0




def t6_1572root : Job := ⟨plan7954,[],none,⟨15,15,0⟩⟩
def t6_1572jobs0 : List Job := [⟨plan7954,[],none,⟨15,15,0⟩⟩]

def t6_1572jobs : List Job := t6_1572jobs0




def t6_1573root : Job := ⟨plan7955,[],none,⟨15,15,0⟩⟩
def t6_1573jobs0 : List Job := [⟨plan7955,[],none,⟨15,15,0⟩⟩]

def t6_1573jobs : List Job := t6_1573jobs0




def t6_1574root : Job := ⟨plan7956,[],none,⟨15,15,0⟩⟩
def t6_1574jobs0 : List Job := [⟨plan7956,[],none,⟨15,15,0⟩⟩]

def t6_1574jobs : List Job := t6_1574jobs0




def t6_1575root : Job := ⟨plan7957,[],none,⟨15,15,0⟩⟩
def t6_1575jobs0 : List Job := [⟨plan7957,[],none,⟨15,15,0⟩⟩]

def t6_1575jobs : List Job := t6_1575jobs0




def t6_1576root : Job := ⟨plan7958,[],none,⟨15,15,0⟩⟩
def t6_1576jobs0 : List Job := [⟨plan7958,[],none,⟨15,15,0⟩⟩]

def t6_1576jobs : List Job := t6_1576jobs0




def t6_1577root : Job := ⟨plan7959,[],none,⟨15,15,0⟩⟩
def t6_1577jobs0 : List Job := [⟨plan7959,[],none,⟨15,15,0⟩⟩]

def t6_1577jobs : List Job := t6_1577jobs0




def t6_1578root : Job := ⟨plan7960,[],none,⟨15,15,0⟩⟩
def t6_1578jobs0 : List Job := [⟨plan7960,[],none,⟨15,15,0⟩⟩]

def t6_1578jobs : List Job := t6_1578jobs0




def t6_1579root : Job := ⟨plan7961,[],none,⟨15,15,0⟩⟩
def t6_1579jobs0 : List Job := [⟨plan7961,[],none,⟨15,15,0⟩⟩]

def t6_1579jobs : List Job := t6_1579jobs0




def t6_1580root : Job := ⟨plan7962,[],none,⟨15,15,0⟩⟩
def t6_1580jobs0 : List Job := [⟨plan7962,[],none,⟨15,15,0⟩⟩]

def t6_1580jobs : List Job := t6_1580jobs0




def t6_1581root : Job := ⟨plan7963,[],none,⟨15,15,0⟩⟩
def t6_1581jobs0 : List Job := [⟨plan7963,[],none,⟨15,15,0⟩⟩]

def t6_1581jobs : List Job := t6_1581jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


