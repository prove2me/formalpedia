-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks044
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks044
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:24:01.649984+00:00
-- url     : https://prove2.me/theorems/74c3e15c-2be9-4ffb-bdbf-51b7d5e44519
-- title:
--   Endpoint22 Reach Checks044 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks044 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t5_1587root`, `ThreeBoundEndpoint22Reachable.t5_1587jobs0`, `ThreeBoundEndpoint22Reachable.t5_1587jobs`, `ThreeBoundEndpoint22Reachable.t5_1588root`, `ThreeBoundEndpoint22Reachable.t5_1588jobs0`, `ThreeBoundEndpoint22Reachable.t5_1588jobs`, `ThreeBoundEndpoint22Reachable.t5_1589root`, `ThreeBoundEndpoint22Reachable.t5_1589jobs0`, `ThreeBoundEndpoint22Reachable.t5_1589jobs`, `ThreeBoundEndpoint22Reachable.t5_1590root`, `ThreeBoundEndpoint22Reachable.t5_1590jobs0`, `ThreeBoundEndpoint22Reachable.t5_1590jobs`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks044.lean, lines 1–481.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans039
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans041
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans046
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans051
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans054
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans055
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

def t5_1574root : Job := ⟨plan4438,[],none,⟨10,3,0⟩⟩
def t5_1574jobs0 : List Job := [⟨plan4438,[],none,⟨10,3,0⟩⟩]

def t5_1574jobs : List Job := t5_1574jobs0




def t5_1575root : Job := ⟨plan4969,[],none,⟨10,6,0⟩⟩
def t5_1575jobs0 : List Job := [⟨plan4969,[],none,⟨10,6,0⟩⟩]

def t5_1575jobs : List Job := t5_1575jobs0




def t5_1576root : Job := ⟨plan4970,[],none,⟨10,6,0⟩⟩
def t5_1576jobs0 : List Job := [⟨plan4970,[],none,⟨10,6,0⟩⟩]

def t5_1576jobs : List Job := t5_1576jobs0




def t5_1577root : Job := ⟨plan4971,[],none,⟨10,6,0⟩⟩
def t5_1577jobs0 : List Job := [⟨plan4971,[],none,⟨10,6,0⟩⟩]

def t5_1577jobs : List Job := t5_1577jobs0




def t5_1578root : Job := ⟨plan4972,[],none,⟨10,6,0⟩⟩
def t5_1578jobs0 : List Job := [⟨plan4972,[],none,⟨10,6,0⟩⟩]

def t5_1578jobs : List Job := t5_1578jobs0




def t5_1579root : Job := ⟨plan4973,[],none,⟨10,6,0⟩⟩
def t5_1579jobs0 : List Job := [⟨plan4973,[],none,⟨10,6,0⟩⟩]

def t5_1579jobs : List Job := t5_1579jobs0




def t5_1580root : Job := ⟨plan4974,[],none,⟨10,6,0⟩⟩
def t5_1580jobs0 : List Job := [⟨plan4974,[],none,⟨10,6,0⟩⟩]

def t5_1580jobs : List Job := t5_1580jobs0




def t5_1581root : Job := ⟨plan5279,[],none,⟨10,10,0⟩⟩
def t5_1581jobs0 : List Job := [⟨plan5279,[],none,⟨10,10,0⟩⟩]

def t5_1581jobs : List Job := t5_1581jobs0




def t5_1582root : Job := ⟨plan5280,[],none,⟨10,10,0⟩⟩
def t5_1582jobs0 : List Job := [⟨plan5280,[],none,⟨10,10,0⟩⟩]

def t5_1582jobs : List Job := t5_1582jobs0




def t5_1583root : Job := ⟨plan5281,[],none,⟨10,10,0⟩⟩
def t5_1583jobs0 : List Job := [⟨plan5281,[],none,⟨10,10,0⟩⟩]

def t5_1583jobs : List Job := t5_1583jobs0




def t5_1584root : Job := ⟨plan5282,[],none,⟨10,10,0⟩⟩
def t5_1584jobs0 : List Job := [⟨plan5282,[],none,⟨10,10,0⟩⟩]

def t5_1584jobs : List Job := t5_1584jobs0




def t5_1585root : Job := ⟨plan5283,[],none,⟨10,10,0⟩⟩
def t5_1585jobs0 : List Job := [⟨plan5283,[],none,⟨10,10,0⟩⟩]

def t5_1585jobs : List Job := t5_1585jobs0




def t5_1586root : Job := ⟨plan5284,[],none,⟨10,10,0⟩⟩
def t5_1586jobs0 : List Job := [⟨plan5284,[],none,⟨10,10,0⟩⟩]

def t5_1586jobs : List Job := t5_1586jobs0




def t5_1587root : Job := ⟨plan5285,[],none,⟨10,10,0⟩⟩
def t5_1587jobs0 : List Job := [⟨plan5285,[],none,⟨10,10,0⟩⟩]

def t5_1587jobs : List Job := t5_1587jobs0




def t5_1588root : Job := ⟨plan4439,[],none,⟨10,3,0⟩⟩
def t5_1588jobs0 : List Job := [⟨plan4439,[],none,⟨10,3,0⟩⟩]

def t5_1588jobs : List Job := t5_1588jobs0




def t5_1589root : Job := ⟨plan4975,[],none,⟨10,6,0⟩⟩
def t5_1589jobs0 : List Job := [⟨plan4975,[],none,⟨10,6,0⟩⟩]

def t5_1589jobs : List Job := t5_1589jobs0




def t5_1590root : Job := ⟨plan4976,[],none,⟨10,6,0⟩⟩
def t5_1590jobs0 : List Job := [⟨plan4976,[],none,⟨10,6,0⟩⟩]

def t5_1590jobs : List Job := t5_1590jobs0




def t5_1591root : Job := ⟨plan4977,[],none,⟨10,6,0⟩⟩
def t5_1591jobs0 : List Job := [⟨plan4977,[],none,⟨10,6,0⟩⟩]

def t5_1591jobs : List Job := t5_1591jobs0




def t5_1592root : Job := ⟨plan5286,[],none,⟨10,10,0⟩⟩
def t5_1592jobs0 : List Job := [⟨plan5286,[],none,⟨10,10,0⟩⟩]

def t5_1592jobs : List Job := t5_1592jobs0




def t5_1593root : Job := ⟨plan5287,[],none,⟨10,10,0⟩⟩
def t5_1593jobs0 : List Job := [⟨plan5287,[],none,⟨10,10,0⟩⟩]

def t5_1593jobs : List Job := t5_1593jobs0




def t5_1594root : Job := ⟨plan5288,[],none,⟨10,10,0⟩⟩
def t5_1594jobs0 : List Job := [⟨plan5288,[],none,⟨10,10,0⟩⟩]

def t5_1594jobs : List Job := t5_1594jobs0




def t5_1595root : Job := ⟨plan5289,[],none,⟨10,10,0⟩⟩
def t5_1595jobs0 : List Job := [⟨plan5289,[],none,⟨10,10,0⟩⟩]

def t5_1595jobs : List Job := t5_1595jobs0




def t5_1596root : Job := ⟨plan4978,[],none,⟨10,6,0⟩⟩
def t5_1596jobs0 : List Job := [⟨plan4978,[],none,⟨10,6,0⟩⟩]

def t5_1596jobs : List Job := t5_1596jobs0




def t5_1597root : Job := ⟨plan5290,[],none,⟨10,10,0⟩⟩
def t5_1597jobs0 : List Job := [⟨plan5290,[],none,⟨10,10,0⟩⟩]

def t5_1597jobs : List Job := t5_1597jobs0




def t5_1598root : Job := ⟨plan5291,[],none,⟨10,10,0⟩⟩
def t5_1598jobs0 : List Job := [⟨plan5291,[],none,⟨10,10,0⟩⟩]

def t5_1598jobs : List Job := t5_1598jobs0




def t5_1599root : Job := ⟨plan5292,[],none,⟨10,10,0⟩⟩
def t5_1599jobs0 : List Job := [⟨plan5292,[],none,⟨10,10,0⟩⟩]

def t5_1599jobs : List Job := t5_1599jobs0




def t5_1600root : Job := ⟨plan5293,[],none,⟨10,10,0⟩⟩
def t5_1600jobs0 : List Job := [⟨plan5293,[],none,⟨10,10,0⟩⟩]

def t5_1600jobs : List Job := t5_1600jobs0




def t5_1601root : Job := ⟨plan5294,[],none,⟨10,10,0⟩⟩
def t5_1601jobs0 : List Job := [⟨plan5294,[],none,⟨10,10,0⟩⟩]

def t5_1601jobs : List Job := t5_1601jobs0




def t5_1602root : Job := ⟨plan5295,[],none,⟨10,10,0⟩⟩
def t5_1602jobs0 : List Job := [⟨plan5295,[],none,⟨10,10,0⟩⟩]

def t5_1602jobs : List Job := t5_1602jobs0




def t5_1603root : Job := ⟨plan5296,[],none,⟨10,10,0⟩⟩
def t5_1603jobs0 : List Job := [⟨plan5296,[],none,⟨10,10,0⟩⟩]

def t5_1603jobs : List Job := t5_1603jobs0




def t5_1604root : Job := ⟨plan5297,[],none,⟨10,10,0⟩⟩
def t5_1604jobs0 : List Job := [⟨plan5297,[],none,⟨10,10,0⟩⟩]

def t5_1604jobs : List Job := t5_1604jobs0




def t5_1605root : Job := ⟨plan5298,[],none,⟨10,10,0⟩⟩
def t5_1605jobs0 : List Job := [⟨plan5298,[],none,⟨10,10,0⟩⟩]

def t5_1605jobs : List Job := t5_1605jobs0




def t5_1606root : Job := ⟨plan5299,[],none,⟨10,10,0⟩⟩
def t5_1606jobs0 : List Job := [⟨plan5299,[],none,⟨10,10,0⟩⟩]

def t5_1606jobs : List Job := t5_1606jobs0




def t5_1607root : Job := ⟨plan5300,[],none,⟨10,10,0⟩⟩
def t5_1607jobs0 : List Job := [⟨plan5300,[],none,⟨10,10,0⟩⟩]

def t5_1607jobs : List Job := t5_1607jobs0




def t5_1608root : Job := ⟨plan5301,[],none,⟨10,10,0⟩⟩
def t5_1608jobs0 : List Job := [⟨plan5301,[],none,⟨10,10,0⟩⟩]

def t5_1608jobs : List Job := t5_1608jobs0




def t5_1609root : Job := ⟨plan3758,[],none,⟨10,0,0⟩⟩
def t5_1609jobs0 : List Job := [⟨plan3758,[],none,⟨10,0,0⟩⟩]

def t5_1609jobs : List Job := t5_1609jobs0




def t5_1610root : Job := ⟨plan3996,[],none,⟨10,1,0⟩⟩
def t5_1610jobs0 : List Job := [⟨plan2627,[⟨9,0,1⟩],(some ⟨9,0,1⟩),⟨10,0,(-1)⟩⟩,⟨plan2627,[⟨9,1,0⟩],(some ⟨9,1,0⟩),⟨9,1,1⟩⟩,⟨plan2627,[⟨9,1,1⟩],(some ⟨9,1,1⟩),⟨9,0,0⟩⟩,⟨plan2627,[⟨9,2,0⟩],(some ⟨9,2,0⟩),⟨8,1,2⟩⟩]

def t5_1610jobs1 : List Job := [⟨plan2627,[⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨8,0,1⟩⟩]

def t5_1610jobs : List Job := t5_1610jobs0++t5_1610jobs1




def t5_1611root : Job := ⟨plan3997,[],none,⟨10,1,0⟩⟩
def t5_1611jobs0 : List Job := [⟨plan2628,[⟨9,0,1⟩],(some ⟨9,0,1⟩),⟨10,0,(-1)⟩⟩,⟨plan2628,[⟨9,1,0⟩],(some ⟨9,1,0⟩),⟨9,1,1⟩⟩,⟨plan2628,[⟨9,1,1⟩],(some ⟨9,1,1⟩),⟨9,0,0⟩⟩,⟨plan2628,[⟨9,2,0⟩],(some ⟨9,2,0⟩),⟨8,1,2⟩⟩]

def t5_1611jobs1 : List Job := [⟨plan2628,[⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨8,0,1⟩⟩]

def t5_1611jobs : List Job := t5_1611jobs0++t5_1611jobs1




def t5_1612root : Job := ⟨plan3998,[],none,⟨10,1,0⟩⟩
def t5_1612jobs0 : List Job := [⟨plan2629,[⟨9,0,1⟩],(some ⟨9,0,1⟩),⟨10,0,(-1)⟩⟩,⟨plan2629,[⟨9,1,0⟩],(some ⟨9,1,0⟩),⟨9,1,1⟩⟩,⟨plan2629,[⟨9,1,1⟩],(some ⟨9,1,1⟩),⟨9,0,0⟩⟩,⟨plan2629,[⟨9,2,0⟩],(some ⟨9,2,0⟩),⟨8,1,2⟩⟩]

def t5_1612jobs1 : List Job := [⟨plan2629,[⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨8,0,1⟩⟩]

def t5_1612jobs : List Job := t5_1612jobs0++t5_1612jobs1




def t5_1613root : Job := ⟨plan4440,[],none,⟨10,3,0⟩⟩
def t5_1613jobs0 : List Job := [⟨plan2762,[⟨9,0,2⟩],(some ⟨9,0,2⟩),⟨10,1,(-2)⟩⟩,⟨plan2762,[⟨9,1,1⟩],(some ⟨9,1,1⟩),⟨9,2,0⟩⟩,⟨plan2762,[⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨9,1,(-1)⟩⟩,⟨plan2762,[⟨9,2,0⟩],(some ⟨9,2,0⟩),⟨8,3,2⟩⟩]

def t5_1613jobs1 : List Job := [⟨plan2762,[⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨8,2,1⟩⟩,⟨plan2762,[⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨8,1,0⟩⟩]

def t5_1613jobs : List Job := t5_1613jobs0++t5_1613jobs1




def t5_1614root : Job := ⟨plan4441,[],none,⟨10,3,0⟩⟩
def t5_1614jobs0 : List Job := [⟨plan2763,[⟨9,0,2⟩],(some ⟨9,0,2⟩),⟨10,1,(-2)⟩⟩,⟨plan2763,[⟨9,1,1⟩],(some ⟨9,1,1⟩),⟨9,2,0⟩⟩]

def t5_1614jobs1 : List Job := [⟨plan2763,[⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨9,1,(-1)⟩⟩,⟨plan2763,[⟨9,2,0⟩],(some ⟨9,2,0⟩),⟨8,3,2⟩⟩]

def t5_1614jobs2 : List Job := [⟨plan2763,[⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨8,2,1⟩⟩]

def t5_1614jobs3 : List Job := [⟨plan2763,[⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨8,1,0⟩⟩]

def t5_1614jobs : List Job := t5_1614jobs0++t5_1614jobs1++t5_1614jobs2++t5_1614jobs3



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


