-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks144
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks144
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:32:42.695766+00:00
-- url     : https://prove2.me/theorems/523e2403-ca21-4e6a-8167-0cdb53fa893a
-- title:
--   Endpoint22 Reach Checks144 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks144 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_1595root`, `ThreeBoundEndpoint22Reachable.t6_1595jobs0`, `ThreeBoundEndpoint22Reachable.t6_1595jobs`, `ThreeBoundEndpoint22Reachable.t6_1596root`, `ThreeBoundEndpoint22Reachable.t6_1596jobs0`, `ThreeBoundEndpoint22Reachable.t6_1596jobs`, `ThreeBoundEndpoint22Reachable.t6_1597root`, `ThreeBoundEndpoint22Reachable.t6_1597jobs0`, `ThreeBoundEndpoint22Reachable.t6_1597jobs`, `ThreeBoundEndpoint22Reachable.t6_1598root`, `ThreeBoundEndpoint22Reachable.t6_1598jobs0`, `ThreeBoundEndpoint22Reachable.t6_1598jobs`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks144.lean, lines 1–688.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans066
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans069
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans074
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans079
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans082
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans083
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

def t6_1582root : Job := ⟨plan7964,[],none,⟨15,15,0⟩⟩
def t6_1582jobs0 : List Job := [⟨plan7964,[],none,⟨15,15,0⟩⟩]

def t6_1582jobs : List Job := t6_1582jobs0




def t6_1583root : Job := ⟨plan7965,[],none,⟨15,15,0⟩⟩
def t6_1583jobs0 : List Job := [⟨plan7965,[],none,⟨15,15,0⟩⟩]

def t6_1583jobs : List Job := t6_1583jobs0




def t6_1584root : Job := ⟨plan7966,[],none,⟨15,15,0⟩⟩
def t6_1584jobs0 : List Job := [⟨plan7966,[],none,⟨15,15,0⟩⟩]

def t6_1584jobs : List Job := t6_1584jobs0




def t6_1585root : Job := ⟨plan7967,[],none,⟨15,15,0⟩⟩
def t6_1585jobs0 : List Job := [⟨plan7967,[],none,⟨15,15,0⟩⟩]

def t6_1585jobs : List Job := t6_1585jobs0




def t6_1586root : Job := ⟨plan7968,[],none,⟨15,15,0⟩⟩
def t6_1586jobs0 : List Job := [⟨plan7968,[],none,⟨15,15,0⟩⟩]

def t6_1586jobs : List Job := t6_1586jobs0




def t6_1587root : Job := ⟨plan7969,[],none,⟨15,15,0⟩⟩
def t6_1587jobs0 : List Job := [⟨plan7969,[],none,⟨15,15,0⟩⟩]

def t6_1587jobs : List Job := t6_1587jobs0




def t6_1588root : Job := ⟨plan7970,[],none,⟨15,15,0⟩⟩
def t6_1588jobs0 : List Job := [⟨plan7970,[],none,⟨15,15,0⟩⟩]

def t6_1588jobs : List Job := t6_1588jobs0




def t6_1589root : Job := ⟨plan7971,[],none,⟨15,15,0⟩⟩
def t6_1589jobs0 : List Job := [⟨plan7971,[],none,⟨15,15,0⟩⟩]

def t6_1589jobs : List Job := t6_1589jobs0




def t6_1590root : Job := ⟨plan7972,[],none,⟨15,15,0⟩⟩
def t6_1590jobs0 : List Job := [⟨plan7972,[],none,⟨15,15,0⟩⟩]

def t6_1590jobs : List Job := t6_1590jobs0




def t6_1591root : Job := ⟨plan7116,[],none,⟨15,6,0⟩⟩
def t6_1591jobs0 : List Job := [⟨plan7116,[],none,⟨15,6,0⟩⟩]

def t6_1591jobs : List Job := t6_1591jobs0




def t6_1592root : Job := ⟨plan7648,[],none,⟨15,10,0⟩⟩
def t6_1592jobs0 : List Job := [⟨plan7648,[],none,⟨15,10,0⟩⟩]

def t6_1592jobs : List Job := t6_1592jobs0




def t6_1593root : Job := ⟨plan7649,[],none,⟨15,10,0⟩⟩
def t6_1593jobs0 : List Job := [⟨plan7649,[],none,⟨15,10,0⟩⟩]

def t6_1593jobs : List Job := t6_1593jobs0




def t6_1594root : Job := ⟨plan7650,[],none,⟨15,10,0⟩⟩
def t6_1594jobs0 : List Job := [⟨plan7650,[],none,⟨15,10,0⟩⟩]

def t6_1594jobs : List Job := t6_1594jobs0




def t6_1595root : Job := ⟨plan6680,[],none,⟨15,3,0⟩⟩
def t6_1595jobs0 : List Job := [⟨plan6680,[],none,⟨15,3,0⟩⟩]

def t6_1595jobs : List Job := t6_1595jobs0




def t6_1596root : Job := ⟨plan7117,[],none,⟨15,6,0⟩⟩
def t6_1596jobs0 : List Job := [⟨plan7117,[],none,⟨15,6,0⟩⟩]

def t6_1596jobs : List Job := t6_1596jobs0




def t6_1597root : Job := ⟨plan7118,[],none,⟨15,6,0⟩⟩
def t6_1597jobs0 : List Job := [⟨plan7118,[],none,⟨15,6,0⟩⟩]

def t6_1597jobs : List Job := t6_1597jobs0




def t6_1598root : Job := ⟨plan7119,[],none,⟨15,6,0⟩⟩
def t6_1598jobs0 : List Job := [⟨plan7119,[],none,⟨15,6,0⟩⟩]

def t6_1598jobs : List Job := t6_1598jobs0




def t6_1599root : Job := ⟨plan7651,[],none,⟨15,10,0⟩⟩
def t6_1599jobs0 : List Job := [⟨plan7651,[],none,⟨15,10,0⟩⟩]

def t6_1599jobs : List Job := t6_1599jobs0




def t6_1600root : Job := ⟨plan7652,[],none,⟨15,10,0⟩⟩
def t6_1600jobs0 : List Job := [⟨plan7652,[],none,⟨15,10,0⟩⟩]

def t6_1600jobs : List Job := t6_1600jobs0




def t6_1601root : Job := ⟨plan7653,[],none,⟨15,10,0⟩⟩
def t6_1601jobs0 : List Job := [⟨plan7653,[],none,⟨15,10,0⟩⟩]

def t6_1601jobs : List Job := t6_1601jobs0




def t6_1602root : Job := ⟨plan7654,[],none,⟨15,10,0⟩⟩
def t6_1602jobs0 : List Job := [⟨plan7654,[],none,⟨15,10,0⟩⟩]

def t6_1602jobs : List Job := t6_1602jobs0




def t6_1603root : Job := ⟨plan7655,[],none,⟨15,10,0⟩⟩
def t6_1603jobs0 : List Job := [⟨plan7655,[],none,⟨15,10,0⟩⟩]

def t6_1603jobs : List Job := t6_1603jobs0




def t6_1604root : Job := ⟨plan7656,[],none,⟨15,10,0⟩⟩
def t6_1604jobs0 : List Job := [⟨plan7656,[],none,⟨15,10,0⟩⟩]

def t6_1604jobs : List Job := t6_1604jobs0




def t6_1605root : Job := ⟨plan7657,[],none,⟨15,10,0⟩⟩
def t6_1605jobs0 : List Job := [⟨plan7657,[],none,⟨15,10,0⟩⟩]

def t6_1605jobs : List Job := t6_1605jobs0




def t6_1606root : Job := ⟨plan7973,[],none,⟨15,15,0⟩⟩
def t6_1606jobs0 : List Job := [⟨plan7973,[],none,⟨15,15,0⟩⟩]

def t6_1606jobs : List Job := t6_1606jobs0




def t6_1607root : Job := ⟨plan7974,[],none,⟨15,15,0⟩⟩
def t6_1607jobs0 : List Job := [⟨plan7974,[],none,⟨15,15,0⟩⟩]

def t6_1607jobs : List Job := t6_1607jobs0




def t6_1608root : Job := ⟨plan7975,[],none,⟨15,15,0⟩⟩
def t6_1608jobs0 : List Job := [⟨plan7975,[],none,⟨15,15,0⟩⟩]

def t6_1608jobs : List Job := t6_1608jobs0




def t6_1609root : Job := ⟨plan7976,[],none,⟨15,15,0⟩⟩
def t6_1609jobs0 : List Job := [⟨plan7976,[],none,⟨15,15,0⟩⟩]

def t6_1609jobs : List Job := t6_1609jobs0




def t6_1610root : Job := ⟨plan7977,[],none,⟨15,15,0⟩⟩
def t6_1610jobs0 : List Job := [⟨plan7977,[],none,⟨15,15,0⟩⟩]

def t6_1610jobs : List Job := t6_1610jobs0




def t6_1611root : Job := ⟨plan7978,[],none,⟨15,15,0⟩⟩
def t6_1611jobs0 : List Job := [⟨plan7978,[],none,⟨15,15,0⟩⟩]

def t6_1611jobs : List Job := t6_1611jobs0




def t6_1612root : Job := ⟨plan7979,[],none,⟨15,15,0⟩⟩
def t6_1612jobs0 : List Job := [⟨plan7979,[],none,⟨15,15,0⟩⟩]

def t6_1612jobs : List Job := t6_1612jobs0




def t6_1613root : Job := ⟨plan7980,[],none,⟨15,15,0⟩⟩
def t6_1613jobs0 : List Job := [⟨plan7980,[],none,⟨15,15,0⟩⟩]

def t6_1613jobs : List Job := t6_1613jobs0




def t6_1614root : Job := ⟨plan7981,[],none,⟨15,15,0⟩⟩
def t6_1614jobs0 : List Job := [⟨plan7981,[],none,⟨15,15,0⟩⟩]

def t6_1614jobs : List Job := t6_1614jobs0




def t6_1615root : Job := ⟨plan7982,[],none,⟨15,15,0⟩⟩
def t6_1615jobs0 : List Job := [⟨plan7982,[],none,⟨15,15,0⟩⟩]

def t6_1615jobs : List Job := t6_1615jobs0




def t6_1616root : Job := ⟨plan7983,[],none,⟨15,15,0⟩⟩
def t6_1616jobs0 : List Job := [⟨plan7983,[],none,⟨15,15,0⟩⟩]

def t6_1616jobs : List Job := t6_1616jobs0




def t6_1617root : Job := ⟨plan7658,[],none,⟨15,10,0⟩⟩
def t6_1617jobs0 : List Job := [⟨plan7658,[],none,⟨15,10,0⟩⟩]

def t6_1617jobs : List Job := t6_1617jobs0




def t6_1618root : Job := ⟨plan7984,[],none,⟨15,15,0⟩⟩
def t6_1618jobs0 : List Job := [⟨plan7984,[],none,⟨15,15,0⟩⟩]

def t6_1618jobs : List Job := t6_1618jobs0




def t6_1619root : Job := ⟨plan7985,[],none,⟨15,15,0⟩⟩
def t6_1619jobs0 : List Job := [⟨plan7985,[],none,⟨15,15,0⟩⟩]

def t6_1619jobs : List Job := t6_1619jobs0




def t6_1620root : Job := ⟨plan7986,[],none,⟨15,15,0⟩⟩
def t6_1620jobs0 : List Job := [⟨plan7986,[],none,⟨15,15,0⟩⟩]

def t6_1620jobs : List Job := t6_1620jobs0




def t6_1621root : Job := ⟨plan7987,[],none,⟨15,15,0⟩⟩
def t6_1621jobs0 : List Job := [⟨plan7987,[],none,⟨15,15,0⟩⟩]

def t6_1621jobs : List Job := t6_1621jobs0




def t6_1622root : Job := ⟨plan7988,[],none,⟨15,15,0⟩⟩
def t6_1622jobs0 : List Job := [⟨plan7988,[],none,⟨15,15,0⟩⟩]

def t6_1622jobs : List Job := t6_1622jobs0




def t6_1623root : Job := ⟨plan7989,[],none,⟨15,15,0⟩⟩
def t6_1623jobs0 : List Job := [⟨plan7989,[],none,⟨15,15,0⟩⟩]

def t6_1623jobs : List Job := t6_1623jobs0




def t6_1624root : Job := ⟨plan6429,[],none,⟨15,1,0⟩⟩
def t6_1624jobs0 : List Job := [⟨plan6429,[],none,⟨15,1,0⟩⟩]

def t6_1624jobs : List Job := t6_1624jobs0




def t6_1625root : Job := ⟨plan6681,[],none,⟨15,3,0⟩⟩
def t6_1625jobs0 : List Job := [⟨plan6681,[],none,⟨15,3,0⟩⟩]

def t6_1625jobs : List Job := t6_1625jobs0




def t6_1626root : Job := ⟨plan6682,[],none,⟨15,3,0⟩⟩
def t6_1626jobs0 : List Job := [⟨plan6682,[],none,⟨15,3,0⟩⟩]

def t6_1626jobs : List Job := t6_1626jobs0




def t6_1627root : Job := ⟨plan6683,[],none,⟨15,3,0⟩⟩
def t6_1627jobs0 : List Job := [⟨plan6683,[],none,⟨15,3,0⟩⟩]

def t6_1627jobs : List Job := t6_1627jobs0




def t6_1628root : Job := ⟨plan7120,[],none,⟨15,6,0⟩⟩
def t6_1628jobs0 : List Job := [⟨plan7120,[],none,⟨15,6,0⟩⟩]

def t6_1628jobs : List Job := t6_1628jobs0




def t6_1629root : Job := ⟨plan7121,[],none,⟨15,6,0⟩⟩
def t6_1629jobs0 : List Job := [⟨plan5715,[⟨8,0,3⟩],(some ⟨8,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5715,[⟨8,1,2⟩],(some ⟨8,1,2⟩),⟨14,4,(-1)⟩⟩]

def t6_1629jobs1 : List Job := [⟨plan5715,[⟨8,1,3⟩],(some ⟨8,1,3⟩),⟨14,3,(-2)⟩⟩]

def t6_1629jobs : List Job := t6_1629jobs0++t6_1629jobs1




def t6_1630root : Job := ⟨plan7122,[],none,⟨15,6,0⟩⟩
def t6_1630jobs0 : List Job := [⟨plan7122,[],none,⟨15,6,0⟩⟩]

def t6_1630jobs : List Job := t6_1630jobs0




def t6_1631root : Job := ⟨plan7123,[],none,⟨15,6,0⟩⟩
def t6_1631jobs0 : List Job := [⟨plan5717,[⟨8,0,3⟩],(some ⟨8,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5717,[⟨8,1,2⟩],(some ⟨8,1,2⟩),⟨14,4,(-1)⟩⟩]

def t6_1631jobs1 : List Job := [⟨plan5717,[⟨8,1,3⟩],(some ⟨8,1,3⟩),⟨14,3,(-2)⟩⟩]

def t6_1631jobs : List Job := t6_1631jobs0++t6_1631jobs1




def t6_1632root : Job := ⟨plan7124,[],none,⟨15,6,0⟩⟩
def t6_1632jobs0 : List Job := [⟨plan5718,[⟨8,0,3⟩],(some ⟨8,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5718,[⟨8,1,2⟩],(some ⟨8,1,2⟩),⟨14,4,(-1)⟩⟩]

def t6_1632jobs1 : List Job := [⟨plan5718,[⟨8,1,3⟩],(some ⟨8,1,3⟩),⟨14,3,(-2)⟩⟩]

def t6_1632jobs : List Job := t6_1632jobs0++t6_1632jobs1




def t6_1633root : Job := ⟨plan7125,[],none,⟨15,6,0⟩⟩
def t6_1633jobs0 : List Job := [⟨plan7125,[],none,⟨15,6,0⟩⟩]

def t6_1633jobs : List Job := t6_1633jobs0




def t6_1634root : Job := ⟨plan7659,[],none,⟨15,10,0⟩⟩
def t6_1634jobs0 : List Job := [⟨plan7659,[],none,⟨15,10,0⟩⟩]

def t6_1634jobs : List Job := t6_1634jobs0




def t6_1635root : Job := ⟨plan7660,[],none,⟨15,10,0⟩⟩
def t6_1635jobs0 : List Job := [⟨plan7660,[],none,⟨15,10,0⟩⟩]

def t6_1635jobs : List Job := t6_1635jobs0




def t6_1636root : Job := ⟨plan7661,[],none,⟨15,10,0⟩⟩
def t6_1636jobs0 : List Job := [⟨plan7661,[],none,⟨15,10,0⟩⟩]

def t6_1636jobs : List Job := t6_1636jobs0




def t6_1637root : Job := ⟨plan7662,[],none,⟨15,10,0⟩⟩
def t6_1637jobs0 : List Job := [⟨plan5930,[⟨8,0,4⟩],(some ⟨8,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5930,[⟨8,1,3⟩],(some ⟨8,1,3⟩),⟨14,7,(-2)⟩⟩]

def t6_1637jobs1 : List Job := [⟨plan5930,[⟨8,1,4⟩],(some ⟨8,1,4⟩),⟨14,6,(-3)⟩⟩]

def t6_1637jobs : List Job := t6_1637jobs0++t6_1637jobs1




def t6_1638root : Job := ⟨plan7663,[],none,⟨15,10,0⟩⟩
def t6_1638jobs0 : List Job := [⟨plan7663,[],none,⟨15,10,0⟩⟩]

def t6_1638jobs : List Job := t6_1638jobs0




def t6_1639root : Job := ⟨plan7664,[],none,⟨15,10,0⟩⟩
def t6_1639jobs0 : List Job := [⟨plan7664,[],none,⟨15,10,0⟩⟩]

def t6_1639jobs : List Job := t6_1639jobs0




def t6_1640root : Job := ⟨plan7665,[],none,⟨15,10,0⟩⟩
def t6_1640jobs0 : List Job := [⟨plan5933,[⟨8,0,4⟩],(some ⟨8,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5933,[⟨8,1,3⟩],(some ⟨8,1,3⟩),⟨14,7,(-2)⟩⟩]

def t6_1640jobs1 : List Job := [⟨plan5933,[⟨8,1,4⟩],(some ⟨8,1,4⟩),⟨14,6,(-3)⟩⟩]

def t6_1640jobs : List Job := t6_1640jobs0++t6_1640jobs1




def t6_1641root : Job := ⟨plan7666,[],none,⟨15,10,0⟩⟩
def t6_1641jobs0 : List Job := [⟨plan5934,[⟨8,0,4⟩],(some ⟨8,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5934,[⟨8,1,3⟩],(some ⟨8,1,3⟩),⟨14,7,(-2)⟩⟩]

def t6_1641jobs1 : List Job := [⟨plan5934,[⟨8,1,4⟩],(some ⟨8,1,4⟩),⟨14,6,(-3)⟩⟩]

def t6_1641jobs : List Job := t6_1641jobs0++t6_1641jobs1



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


