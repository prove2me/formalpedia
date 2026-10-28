-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks140
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks140
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:31:56.060977+00:00
-- url     : https://prove2.me/theorems/76b7e2d5-99eb-4c29-a91d-e7b67026ec14
-- title:
--   Endpoint22 Reach Checks140 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks140 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_1478jobs`, `ThreeBoundEndpoint22Reachable.t6_1479root`, `ThreeBoundEndpoint22Reachable.t6_1479jobs0`, `ThreeBoundEndpoint22Reachable.t6_1479jobs`, `ThreeBoundEndpoint22Reachable.t6_1480root`, `ThreeBoundEndpoint22Reachable.t6_1480jobs0`, `ThreeBoundEndpoint22Reachable.t6_1480jobs`, `ThreeBoundEndpoint22Reachable.t6_1481root`, `ThreeBoundEndpoint22Reachable.t6_1481jobs0`, `ThreeBoundEndpoint22Reachable.t6_1481jobs`, `ThreeBoundEndpoint22Reachable.t6_1482root`, `ThreeBoundEndpoint22Reachable.t6_1482jobs0`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks140.lean, lines 1–326.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans065
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans066
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans069
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans073
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans079
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

def t6_1466root : Job := ⟨plan7605,[],none,⟨15,10,0⟩⟩
def t6_1466jobs0 : List Job := [⟨plan7605,[],none,⟨15,10,0⟩⟩]

def t6_1466jobs : List Job := t6_1466jobs0




def t6_1467root : Job := ⟨plan6670,[],none,⟨15,3,0⟩⟩
def t6_1467jobs0 : List Job := [⟨plan6670,[],none,⟨15,3,0⟩⟩]

def t6_1467jobs : List Job := t6_1467jobs0




def t6_1468root : Job := ⟨plan7095,[],none,⟨15,6,0⟩⟩
def t6_1468jobs0 : List Job := [⟨plan7095,[],none,⟨15,6,0⟩⟩]

def t6_1468jobs : List Job := t6_1468jobs0




def t6_1469root : Job := ⟨plan7096,[],none,⟨15,6,0⟩⟩
def t6_1469jobs0 : List Job := [⟨plan5603,[⟨8,0,3⟩],(some ⟨8,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5603,[⟨8,1,2⟩],(some ⟨8,1,2⟩),⟨14,4,(-1)⟩⟩]

def t6_1469jobs1 : List Job := [⟨plan5603,[⟨8,1,3⟩],(some ⟨8,1,3⟩),⟨14,3,(-2)⟩⟩]

def t6_1469jobs : List Job := t6_1469jobs0++t6_1469jobs1




def t6_1470root : Job := ⟨plan7097,[],none,⟨15,6,0⟩⟩
def t6_1470jobs0 : List Job := [⟨plan7097,[],none,⟨15,6,0⟩⟩]

def t6_1470jobs : List Job := t6_1470jobs0




def t6_1471root : Job := ⟨plan7606,[],none,⟨15,10,0⟩⟩
def t6_1471jobs0 : List Job := [⟨plan7606,[],none,⟨15,10,0⟩⟩]

def t6_1471jobs : List Job := t6_1471jobs0




def t6_1472root : Job := ⟨plan7607,[],none,⟨15,10,0⟩⟩
def t6_1472jobs0 : List Job := [⟨plan7607,[],none,⟨15,10,0⟩⟩]

def t6_1472jobs : List Job := t6_1472jobs0




def t6_1473root : Job := ⟨plan7608,[],none,⟨15,10,0⟩⟩
def t6_1473jobs0 : List Job := [⟨plan7608,[],none,⟨15,10,0⟩⟩]

def t6_1473jobs : List Job := t6_1473jobs0




def t6_1474root : Job := ⟨plan7609,[],none,⟨15,10,0⟩⟩
def t6_1474jobs0 : List Job := [⟨plan7609,[],none,⟨15,10,0⟩⟩]

def t6_1474jobs : List Job := t6_1474jobs0




def t6_1475root : Job := ⟨plan7610,[],none,⟨15,10,0⟩⟩
def t6_1475jobs0 : List Job := [⟨plan7610,[],none,⟨15,10,0⟩⟩]

def t6_1475jobs : List Job := t6_1475jobs0




def t6_1476root : Job := ⟨plan7611,[],none,⟨15,10,0⟩⟩
def t6_1476jobs0 : List Job := [⟨plan7611,[],none,⟨15,10,0⟩⟩]

def t6_1476jobs : List Job := t6_1476jobs0




def t6_1477root : Job := ⟨plan7612,[],none,⟨15,10,0⟩⟩
def t6_1477jobs0 : List Job := [⟨plan7612,[],none,⟨15,10,0⟩⟩]

def t6_1477jobs : List Job := t6_1477jobs0




def t6_1478root : Job := ⟨plan7613,[],none,⟨15,10,0⟩⟩
def t6_1478jobs0 : List Job := [⟨plan7613,[],none,⟨15,10,0⟩⟩]

def t6_1478jobs : List Job := t6_1478jobs0




def t6_1479root : Job := ⟨plan7614,[],none,⟨15,10,0⟩⟩
def t6_1479jobs0 : List Job := [⟨plan7614,[],none,⟨15,10,0⟩⟩]

def t6_1479jobs : List Job := t6_1479jobs0




def t6_1480root : Job := ⟨plan7615,[],none,⟨15,10,0⟩⟩
def t6_1480jobs0 : List Job := [⟨plan7615,[],none,⟨15,10,0⟩⟩]

def t6_1480jobs : List Job := t6_1480jobs0




def t6_1481root : Job := ⟨plan7616,[],none,⟨15,10,0⟩⟩
def t6_1481jobs0 : List Job := [⟨plan7616,[],none,⟨15,10,0⟩⟩]

def t6_1481jobs : List Job := t6_1481jobs0




def t6_1482root : Job := ⟨plan6318,[],none,⟨15,0,0⟩⟩
def t6_1482jobs0 : List Job := [⟨plan6318,[],none,⟨15,0,0⟩⟩]

def t6_1482jobs : List Job := t6_1482jobs0




def t6_1483root : Job := ⟨plan6425,[],none,⟨15,1,0⟩⟩
def t6_1483jobs0 : List Job := [⟨plan6425,[],none,⟨15,1,0⟩⟩]

def t6_1483jobs : List Job := t6_1483jobs0




def t6_1484root : Job := ⟨plan6426,[],none,⟨15,1,0⟩⟩
def t6_1484jobs0 : List Job := [⟨plan6426,[],none,⟨15,1,0⟩⟩]

def t6_1484jobs : List Job := t6_1484jobs0




def t6_1485root : Job := ⟨plan6427,[],none,⟨15,1,0⟩⟩
def t6_1485jobs0 : List Job := [⟨plan6427,[],none,⟨15,1,0⟩⟩]

def t6_1485jobs : List Job := t6_1485jobs0




def t6_1486root : Job := ⟨plan6671,[],none,⟨15,3,0⟩⟩
def t6_1486jobs0 : List Job := [⟨plan6671,[],none,⟨15,3,0⟩⟩]

def t6_1486jobs : List Job := t6_1486jobs0




def t6_1487root : Job := ⟨plan6672,[],none,⟨15,3,0⟩⟩
def t6_1487jobs0 : List Job := [⟨plan5481,[⟨8,0,2⟩],(some ⟨8,0,2⟩),⟨15,1,(-2)⟩⟩]

def t6_1487jobs1 : List Job := [⟨plan5481,[⟨8,1,1⟩],(some ⟨8,1,1⟩),⟨14,2,0⟩⟩]

def t6_1487jobs2 : List Job := [⟨plan5481,[⟨8,1,2⟩],(some ⟨8,1,2⟩),⟨14,1,(-1)⟩⟩]

def t6_1487jobs : List Job := t6_1487jobs0++t6_1487jobs1++t6_1487jobs2




def t6_1488root : Job := ⟨plan6673,[],none,⟨15,3,0⟩⟩
def t6_1488jobs0 : List Job := [⟨plan6673,[],none,⟨15,3,0⟩⟩]

def t6_1488jobs : List Job := t6_1488jobs0




def t6_1489root : Job := ⟨plan6674,[],none,⟨15,3,0⟩⟩
def t6_1489jobs0 : List Job := [⟨plan5483,[⟨8,0,2⟩],(some ⟨8,0,2⟩),⟨15,1,(-2)⟩⟩]

def t6_1489jobs1 : List Job := [⟨plan5483,[⟨8,1,1⟩],(some ⟨8,1,1⟩),⟨14,2,0⟩⟩]

def t6_1489jobs2 : List Job := [⟨plan5483,[⟨8,1,2⟩],(some ⟨8,1,2⟩),⟨14,1,(-1)⟩⟩]

def t6_1489jobs : List Job := t6_1489jobs0++t6_1489jobs1++t6_1489jobs2




def t6_1490root : Job := ⟨plan6675,[],none,⟨15,3,0⟩⟩
def t6_1490jobs0 : List Job := [⟨plan5484,[⟨8,0,2⟩],(some ⟨8,0,2⟩),⟨15,1,(-2)⟩⟩]

def t6_1490jobs1 : List Job := [⟨plan5484,[⟨8,1,1⟩],(some ⟨8,1,1⟩),⟨14,2,0⟩⟩]

def t6_1490jobs2 : List Job := [⟨plan5484,[⟨8,1,2⟩],(some ⟨8,1,2⟩),⟨14,1,(-1)⟩⟩]

def t6_1490jobs : List Job := t6_1490jobs0++t6_1490jobs1++t6_1490jobs2




def t6_1491root : Job := ⟨plan6676,[],none,⟨15,3,0⟩⟩
def t6_1491jobs0 : List Job := [⟨plan6676,[],none,⟨15,3,0⟩⟩]

def t6_1491jobs : List Job := t6_1491jobs0




def t6_1492root : Job := ⟨plan7098,[],none,⟨15,6,0⟩⟩
def t6_1492jobs0 : List Job := [⟨plan7098,[],none,⟨15,6,0⟩⟩]

def t6_1492jobs : List Job := t6_1492jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


