-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks142
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks142
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:32:00.517081+00:00
-- url     : https://prove2.me/theorems/82e7b8a9-c06f-4246-bb0c-ed3fa0e3e3ee
-- title:
--   Endpoint22 Reach Checks142 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks142 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_1514root`, `ThreeBoundEndpoint22Reachable.t6_1514jobs0`, `ThreeBoundEndpoint22Reachable.t6_1514jobs1`, `ThreeBoundEndpoint22Reachable.t6_1514jobs`, `ThreeBoundEndpoint22Reachable.t6_1515root`, `ThreeBoundEndpoint22Reachable.t6_1515jobs0`, `ThreeBoundEndpoint22Reachable.t6_1515jobs`, `ThreeBoundEndpoint22Reachable.t6_1506root`, `ThreeBoundEndpoint22Reachable.t6_1506jobs0`, `ThreeBoundEndpoint22Reachable.t6_1506jobs1`, `ThreeBoundEndpoint22Reachable.t6_1506jobs`, `ThreeBoundEndpoint22Reachable.t6_1507root`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks142.lean, lines 1–154.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
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

def t6_1505root : Job := ⟨plan7620,[],none,⟨15,10,0⟩⟩
def t6_1505jobs0 : List Job := [⟨plan5773,[⟨8,0,4⟩],(some ⟨8,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5773,[⟨8,1,3⟩],(some ⟨8,1,3⟩),⟨14,7,(-2)⟩⟩]

def t6_1505jobs1 : List Job := [⟨plan5773,[⟨8,1,4⟩],(some ⟨8,1,4⟩),⟨14,6,(-3)⟩⟩]

def t6_1505jobs : List Job := t6_1505jobs0++t6_1505jobs1




def t6_1506root : Job := ⟨plan7621,[],none,⟨15,10,0⟩⟩
def t6_1506jobs0 : List Job := [⟨plan5774,[⟨8,0,4⟩],(some ⟨8,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5774,[⟨8,1,3⟩],(some ⟨8,1,3⟩),⟨14,7,(-2)⟩⟩]

def t6_1506jobs1 : List Job := [⟨plan5774,[⟨8,1,4⟩],(some ⟨8,1,4⟩),⟨14,6,(-3)⟩⟩]

def t6_1506jobs : List Job := t6_1506jobs0++t6_1506jobs1




def t6_1507root : Job := ⟨plan7622,[],none,⟨15,10,0⟩⟩
def t6_1507jobs0 : List Job := [⟨plan7622,[],none,⟨15,10,0⟩⟩]

def t6_1507jobs : List Job := t6_1507jobs0




def t6_1508root : Job := ⟨plan7623,[],none,⟨15,10,0⟩⟩
def t6_1508jobs0 : List Job := [⟨plan5776,[⟨8,0,4⟩],(some ⟨8,0,4⟩),⟨15,6,(-4)⟩⟩]

def t6_1508jobs1 : List Job := [⟨plan5776,[⟨8,1,3⟩],(some ⟨8,1,3⟩),⟨14,7,(-2)⟩⟩]

def t6_1508jobs2 : List Job := [⟨plan5776,[⟨8,1,4⟩],(some ⟨8,1,4⟩),⟨14,6,(-3)⟩⟩]

def t6_1508jobs : List Job := t6_1508jobs0++t6_1508jobs1++t6_1508jobs2




def t6_1509root : Job := ⟨plan7624,[],none,⟨15,10,0⟩⟩
def t6_1509jobs0 : List Job := [⟨plan3482,[⟨8,0,4⟩,⟨3,0,5⟩],(some ⟨3,0,5⟩),⟨15,6,(-9)⟩⟩,⟨plan3482,[⟨8,0,4⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3482,[⟨8,0,4⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨13,6,(-7)⟩⟩,⟨plan3482,[⟨8,0,4⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨12,6,(-6)⟩⟩,⟨plan3482,[⟨8,1,3⟩,⟨3,0,5⟩],(some ⟨3,0,5⟩),⟨14,7,(-7)⟩⟩,⟨plan3482,[⟨8,1,3⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨13,7,(-6)⟩⟩,⟨plan3482,[⟨8,1,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,7,(-5)⟩⟩]

def t6_1509jobs1 : List Job := [⟨plan3482,[⟨8,1,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,7,(-4)⟩⟩,⟨plan3482,[⟨8,1,4⟩,⟨3,0,5⟩],(some ⟨3,0,5⟩),⟨14,6,(-8)⟩⟩,⟨plan3482,[⟨8,1,4⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨13,6,(-7)⟩⟩]

def t6_1509jobs2 : List Job := [⟨plan3482,[⟨8,1,4⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,6,(-6)⟩⟩,⟨plan3482,[⟨8,1,4⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,6,(-5)⟩⟩]

def t6_1509jobs : List Job := t6_1509jobs0++t6_1509jobs1++t6_1509jobs2




def t6_1510root : Job := ⟨plan7625,[],none,⟨15,10,0⟩⟩
def t6_1510jobs0 : List Job := [⟨plan5778,[⟨8,0,4⟩],(some ⟨8,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5778,[⟨8,1,3⟩],(some ⟨8,1,3⟩),⟨14,7,(-2)⟩⟩]

def t6_1510jobs1 : List Job := [⟨plan5778,[⟨8,1,4⟩],(some ⟨8,1,4⟩),⟨14,6,(-3)⟩⟩]

def t6_1510jobs : List Job := t6_1510jobs0++t6_1510jobs1




def t6_1511root : Job := ⟨plan7626,[],none,⟨15,10,0⟩⟩
def t6_1511jobs0 : List Job := [⟨plan7626,[],none,⟨15,10,0⟩⟩]

def t6_1511jobs : List Job := t6_1511jobs0




def t6_1512root : Job := ⟨plan7627,[],none,⟨15,10,0⟩⟩
def t6_1512jobs0 : List Job := [⟨plan5780,[⟨8,0,4⟩],(some ⟨8,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5780,[⟨8,1,3⟩],(some ⟨8,1,3⟩),⟨14,7,(-2)⟩⟩]

def t6_1512jobs1 : List Job := [⟨plan5780,[⟨8,1,4⟩],(some ⟨8,1,4⟩),⟨14,6,(-3)⟩⟩]

def t6_1512jobs : List Job := t6_1512jobs0++t6_1512jobs1




def t6_1513root : Job := ⟨plan7628,[],none,⟨15,10,0⟩⟩
def t6_1513jobs0 : List Job := [⟨plan5781,[⟨8,0,4⟩],(some ⟨8,0,4⟩),⟨15,6,(-4)⟩⟩]

def t6_1513jobs1 : List Job := [⟨plan5781,[⟨8,1,3⟩],(some ⟨8,1,3⟩),⟨14,7,(-2)⟩⟩]

def t6_1513jobs2 : List Job := [⟨plan5781,[⟨8,1,4⟩],(some ⟨8,1,4⟩),⟨14,6,(-3)⟩⟩]

def t6_1513jobs : List Job := t6_1513jobs0++t6_1513jobs1++t6_1513jobs2




def t6_1514root : Job := ⟨plan7629,[],none,⟨15,10,0⟩⟩
def t6_1514jobs0 : List Job := [⟨plan5782,[⟨8,0,4⟩],(some ⟨8,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5782,[⟨8,1,3⟩],(some ⟨8,1,3⟩),⟨14,7,(-2)⟩⟩]

def t6_1514jobs1 : List Job := [⟨plan5782,[⟨8,1,4⟩],(some ⟨8,1,4⟩),⟨14,6,(-3)⟩⟩]

def t6_1514jobs : List Job := t6_1514jobs0++t6_1514jobs1




def t6_1515root : Job := ⟨plan7630,[],none,⟨15,10,0⟩⟩
def t6_1515jobs0 : List Job := [⟨plan7630,[],none,⟨15,10,0⟩⟩]

def t6_1515jobs : List Job := t6_1515jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


