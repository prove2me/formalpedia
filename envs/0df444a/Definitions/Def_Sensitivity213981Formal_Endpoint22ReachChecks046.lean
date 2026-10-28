-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks046
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks046
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:26:00.739628+00:00
-- url     : https://prove2.me/theorems/55972c21-c5db-4d00-8695-e2813a1d0714
-- title:
--   Endpoint22 Reach Checks046 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks046 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t5_1632jobs0`, `ThreeBoundEndpoint22Reachable.t5_1632jobs`, `ThreeBoundEndpoint22Reachable.t5_1633root`, `ThreeBoundEndpoint22Reachable.t5_1633jobs0`, `ThreeBoundEndpoint22Reachable.t5_1633jobs`, `ThreeBoundEndpoint22Reachable.t5_1623jobs3`, `ThreeBoundEndpoint22Reachable.t5_1634root`, `ThreeBoundEndpoint22Reachable.t5_1634jobs0`, `ThreeBoundEndpoint22Reachable.t5_1634jobs`, `ThreeBoundEndpoint22Reachable.t5_1635root`, `ThreeBoundEndpoint22Reachable.t5_1635jobs0`, `ThreeBoundEndpoint22Reachable.t5_1635jobs`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks046.lean, lines 1–241.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans041
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans046
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans051
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

def t5_1623root : Job := ⟨plan4983,[],none,⟨10,6,0⟩⟩
def t5_1623jobs0 : List Job := [⟨plan2908,[⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨10,3,(-3)⟩⟩]

def t5_1623jobs1 : List Job := [⟨plan2908,[⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨9,4,(-1)⟩⟩]

def t5_1623jobs2 : List Job := [⟨plan2908,[⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨9,3,(-2)⟩⟩]

def t5_1623jobs3 : List Job := [⟨plan2908,[⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨8,5,1⟩⟩]

def t5_1623jobs4 : List Job := [⟨plan2908,[⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨8,4,0⟩⟩]

def t5_1623jobs : List Job := t5_1623jobs0++t5_1623jobs1++t5_1623jobs2++t5_1623jobs3++t5_1623jobs4




def t5_1624root : Job := ⟨plan4984,[],none,⟨10,6,0⟩⟩
def t5_1624jobs0 : List Job := [⟨plan2909,[⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2909,[⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨9,4,(-1)⟩⟩,⟨plan2909,[⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨9,3,(-2)⟩⟩]

def t5_1624jobs1 : List Job := [⟨plan2909,[⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨8,5,1⟩⟩,⟨plan2909,[⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨8,4,0⟩⟩]

def t5_1624jobs : List Job := t5_1624jobs0++t5_1624jobs1




def t5_1625root : Job := ⟨plan4985,[],none,⟨10,6,0⟩⟩
def t5_1625jobs0 : List Job := [⟨plan2910,[⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2910,[⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨9,4,(-1)⟩⟩,⟨plan2910,[⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨9,3,(-2)⟩⟩,⟨plan2910,[⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨8,5,1⟩⟩]

def t5_1625jobs1 : List Job := [⟨plan2910,[⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨8,4,0⟩⟩]

def t5_1625jobs : List Job := t5_1625jobs0++t5_1625jobs1




def t5_1626root : Job := ⟨plan4986,[],none,⟨10,6,0⟩⟩
def t5_1626jobs0 : List Job := [⟨plan2911,[⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2911,[⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨9,4,(-1)⟩⟩]

def t5_1626jobs1 : List Job := [⟨plan2911,[⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨9,3,(-2)⟩⟩,⟨plan2911,[⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨8,5,1⟩⟩]

def t5_1626jobs2 : List Job := [⟨plan2911,[⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨8,4,0⟩⟩]

def t5_1626jobs : List Job := t5_1626jobs0++t5_1626jobs1++t5_1626jobs2




def t5_1627root : Job := ⟨plan4987,[],none,⟨10,6,0⟩⟩
def t5_1627jobs0 : List Job := [⟨plan2912,[⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2912,[⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨9,4,(-1)⟩⟩,⟨plan2912,[⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨9,3,(-2)⟩⟩]

def t5_1627jobs1 : List Job := [⟨plan2912,[⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨8,5,1⟩⟩,⟨plan2912,[⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨8,4,0⟩⟩]

def t5_1627jobs : List Job := t5_1627jobs0++t5_1627jobs1




def t5_1628root : Job := ⟨plan4988,[],none,⟨10,6,0⟩⟩
def t5_1628jobs0 : List Job := [⟨plan4988,[],none,⟨10,6,0⟩⟩]

def t5_1628jobs : List Job := t5_1628jobs0




def t5_1629root : Job := ⟨plan5302,[],none,⟨10,10,0⟩⟩
def t5_1629jobs0 : List Job := [⟨plan5302,[],none,⟨10,10,0⟩⟩]

def t5_1629jobs : List Job := t5_1629jobs0




def t5_1630root : Job := ⟨plan5303,[],none,⟨10,10,0⟩⟩
def t5_1630jobs0 : List Job := [⟨plan5303,[],none,⟨10,10,0⟩⟩]

def t5_1630jobs : List Job := t5_1630jobs0




def t5_1631root : Job := ⟨plan5304,[],none,⟨10,10,0⟩⟩
def t5_1631jobs0 : List Job := [⟨plan5304,[],none,⟨10,10,0⟩⟩]

def t5_1631jobs : List Job := t5_1631jobs0




def t5_1632root : Job := ⟨plan5305,[],none,⟨10,10,0⟩⟩
def t5_1632jobs0 : List Job := [⟨plan5305,[],none,⟨10,10,0⟩⟩]

def t5_1632jobs : List Job := t5_1632jobs0




def t5_1633root : Job := ⟨plan5306,[],none,⟨10,10,0⟩⟩
def t5_1633jobs0 : List Job := [⟨plan5306,[],none,⟨10,10,0⟩⟩]

def t5_1633jobs : List Job := t5_1633jobs0




def t5_1634root : Job := ⟨plan5307,[],none,⟨10,10,0⟩⟩
def t5_1634jobs0 : List Job := [⟨plan5307,[],none,⟨10,10,0⟩⟩]

def t5_1634jobs : List Job := t5_1634jobs0




def t5_1635root : Job := ⟨plan5308,[],none,⟨10,10,0⟩⟩
def t5_1635jobs0 : List Job := [⟨plan5308,[],none,⟨10,10,0⟩⟩]

def t5_1635jobs : List Job := t5_1635jobs0




def t5_1636root : Job := ⟨plan5309,[],none,⟨10,10,0⟩⟩
def t5_1636jobs0 : List Job := [⟨plan5309,[],none,⟨10,10,0⟩⟩]

def t5_1636jobs : List Job := t5_1636jobs0




def t5_1637root : Job := ⟨plan5310,[],none,⟨10,10,0⟩⟩
def t5_1637jobs0 : List Job := [⟨plan5310,[],none,⟨10,10,0⟩⟩]

def t5_1637jobs : List Job := t5_1637jobs0




def t5_1638root : Job := ⟨plan5311,[],none,⟨10,10,0⟩⟩
def t5_1638jobs0 : List Job := [⟨plan5311,[],none,⟨10,10,0⟩⟩]

def t5_1638jobs : List Job := t5_1638jobs0




def t5_1639root : Job := ⟨plan5312,[],none,⟨10,10,0⟩⟩
def t5_1639jobs0 : List Job := [⟨plan5312,[],none,⟨10,10,0⟩⟩]

def t5_1639jobs : List Job := t5_1639jobs0




def t5_1640root : Job := ⟨plan3999,[],none,⟨10,1,0⟩⟩
def t5_1640jobs0 : List Job := [⟨plan3999,[],none,⟨10,1,0⟩⟩]

def t5_1640jobs : List Job := t5_1640jobs0




def t5_1641root : Job := ⟨plan4446,[],none,⟨10,3,0⟩⟩
def t5_1641jobs0 : List Job := [⟨plan4446,[],none,⟨10,3,0⟩⟩]

def t5_1641jobs : List Job := t5_1641jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


