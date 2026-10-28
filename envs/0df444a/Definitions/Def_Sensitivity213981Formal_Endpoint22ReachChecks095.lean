-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks095
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks095
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:27:47.587491+00:00
-- url     : https://prove2.me/theorems/97399e78-2dde-4a1b-8bcb-c90c6dd53b97
-- title:
--   Endpoint22 Reach Checks095 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks095 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_790jobs0`, `ThreeBoundEndpoint22Reachable.t6_790jobs`, `ThreeBoundEndpoint22Reachable.t6_791root`, `ThreeBoundEndpoint22Reachable.t6_791jobs0`, `ThreeBoundEndpoint22Reachable.t6_791jobs`, `ThreeBoundEndpoint22Reachable.t6_792root`, `ThreeBoundEndpoint22Reachable.t6_792jobs0`, `ThreeBoundEndpoint22Reachable.t6_792jobs1`, `ThreeBoundEndpoint22Reachable.t6_792jobs`, `ThreeBoundEndpoint22Reachable.t6_786jobs1`, `ThreeBoundEndpoint22Reachable.t6_786jobs2`, `ThreeBoundEndpoint22Reachable.t6_786jobs3`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks095.lean, lines 1–121.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans072
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans076
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

def t6_786root : Job := ⟨plan6961,[],none,⟨15,6,0⟩⟩
def t6_786jobs0 : List Job := [⟨plan3367,[⟨2,0,4⟩,⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨15,3,(-7)⟩⟩,⟨plan3367,[⟨2,0,4⟩,⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨14,4,(-5)⟩⟩,⟨plan3367,[⟨2,0,4⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3367,[⟨2,0,4⟩,⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨13,5,(-3)⟩⟩,⟨plan3367,[⟨2,0,4⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨13,4,(-4)⟩⟩,⟨plan3367,[⟨2,0,4⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3367,[⟨2,1,3⟩,⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3367,[⟨2,1,3⟩,⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨13,4,(-4)⟩⟩,⟨plan3367,[⟨2,1,3⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3367,[⟨2,1,3⟩,⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨12,5,(-2)⟩⟩]

def t6_786jobs1 : List Job := [⟨plan3367,[⟨2,1,3⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨12,4,(-3)⟩⟩,⟨plan3367,[⟨2,1,3⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨12,3,(-4)⟩⟩,⟨plan3367,[⟨2,1,4⟩,⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨14,3,(-7)⟩⟩,⟨plan3367,[⟨2,1,4⟩,⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨13,4,(-5)⟩⟩,⟨plan3367,[⟨2,1,4⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨13,3,(-6)⟩⟩]

def t6_786jobs2 : List Job := [⟨plan3367,[⟨2,1,4⟩,⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨12,5,(-3)⟩⟩,⟨plan3367,[⟨2,1,4⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨12,4,(-4)⟩⟩,⟨plan3367,[⟨2,1,4⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨12,3,(-5)⟩⟩,⟨plan3367,[⟨2,2,2⟩,⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨13,3,(-5)⟩⟩]

def t6_786jobs3 : List Job := [⟨plan3367,[⟨2,2,2⟩,⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨12,4,(-3)⟩⟩,⟨plan3367,[⟨2,2,2⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨12,3,(-4)⟩⟩]

def t6_786jobs4 : List Job := [⟨plan3367,[⟨2,2,2⟩,⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨11,5,(-1)⟩⟩]

def t6_786jobs5 : List Job := [⟨plan3367,[⟨2,2,2⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨11,4,(-2)⟩⟩]

def t6_786jobs6 : List Job := [⟨plan3367,[⟨2,2,2⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨11,3,(-3)⟩⟩,⟨plan3367,[⟨2,2,3⟩,⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨13,3,(-6)⟩⟩]

def t6_786jobs7 : List Job := [⟨plan3367,[⟨2,2,3⟩,⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨12,4,(-4)⟩⟩,⟨plan3367,[⟨2,2,3⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨12,3,(-5)⟩⟩]

def t6_786jobs8 : List Job := [⟨plan3367,[⟨2,2,3⟩,⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨11,5,(-2)⟩⟩]

def t6_786jobs9 : List Job := [⟨plan3367,[⟨2,2,3⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨11,4,(-3)⟩⟩]

def t6_786jobs10 : List Job := [⟨plan3367,[⟨2,2,3⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨11,3,(-4)⟩⟩]

def t6_786jobs : List Job := t6_786jobs0++t6_786jobs1++t6_786jobs2++t6_786jobs3++t6_786jobs4++t6_786jobs5++t6_786jobs6++t6_786jobs7++t6_786jobs8++t6_786jobs9++t6_786jobs10




def t6_787root : Job := ⟨plan6962,[],none,⟨15,6,0⟩⟩
def t6_787jobs0 : List Job := [⟨plan3368,[⟨2,0,4⟩,⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨15,3,(-7)⟩⟩,⟨plan3368,[⟨2,0,4⟩,⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨14,4,(-5)⟩⟩,⟨plan3368,[⟨2,0,4⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3368,[⟨2,0,4⟩,⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨13,5,(-3)⟩⟩,⟨plan3368,[⟨2,0,4⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨13,4,(-4)⟩⟩,⟨plan3368,[⟨2,0,4⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3368,[⟨2,1,3⟩,⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3368,[⟨2,1,3⟩,⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨13,4,(-4)⟩⟩,⟨plan3368,[⟨2,1,3⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3368,[⟨2,1,3⟩,⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨12,5,(-2)⟩⟩,⟨plan3368,[⟨2,1,3⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨12,4,(-3)⟩⟩,⟨plan3368,[⟨2,1,3⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨12,3,(-4)⟩⟩,⟨plan3368,[⟨2,1,4⟩,⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨14,3,(-7)⟩⟩,⟨plan3368,[⟨2,1,4⟩,⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨13,4,(-5)⟩⟩,⟨plan3368,[⟨2,1,4⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨13,3,(-6)⟩⟩,⟨plan3368,[⟨2,1,4⟩,⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨12,5,(-3)⟩⟩]

def t6_787jobs1 : List Job := [⟨plan3368,[⟨2,1,4⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨12,4,(-4)⟩⟩,⟨plan3368,[⟨2,1,4⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨12,3,(-5)⟩⟩,⟨plan3368,[⟨2,2,2⟩,⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3368,[⟨2,2,2⟩,⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨12,4,(-3)⟩⟩,⟨plan3368,[⟨2,2,2⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨12,3,(-4)⟩⟩]

def t6_787jobs2 : List Job := [⟨plan3368,[⟨2,2,2⟩,⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨11,5,(-1)⟩⟩,⟨plan3368,[⟨2,2,2⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨11,4,(-2)⟩⟩]

def t6_787jobs3 : List Job := [⟨plan3368,[⟨2,2,2⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨11,3,(-3)⟩⟩,⟨plan3368,[⟨2,2,3⟩,⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨13,3,(-6)⟩⟩,⟨plan3368,[⟨2,2,3⟩,⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨12,4,(-4)⟩⟩,⟨plan3368,[⟨2,2,3⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨12,3,(-5)⟩⟩]

def t6_787jobs4 : List Job := [⟨plan3368,[⟨2,2,3⟩,⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨11,5,(-2)⟩⟩,⟨plan3368,[⟨2,2,3⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨11,4,(-3)⟩⟩]

def t6_787jobs5 : List Job := [⟨plan3368,[⟨2,2,3⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨11,3,(-4)⟩⟩]

def t6_787jobs : List Job := t6_787jobs0++t6_787jobs1++t6_787jobs2++t6_787jobs3++t6_787jobs4++t6_787jobs5




def t6_788root : Job := ⟨plan6963,[],none,⟨15,6,0⟩⟩
def t6_788jobs0 : List Job := [⟨plan6963,[],none,⟨15,6,0⟩⟩]

def t6_788jobs : List Job := t6_788jobs0




def t6_789root : Job := ⟨plan7380,[],none,⟨15,10,0⟩⟩
def t6_789jobs0 : List Job := [⟨plan7380,[],none,⟨15,10,0⟩⟩]

def t6_789jobs : List Job := t6_789jobs0




def t6_790root : Job := ⟨plan7381,[],none,⟨15,10,0⟩⟩
def t6_790jobs0 : List Job := [⟨plan7381,[],none,⟨15,10,0⟩⟩]

def t6_790jobs : List Job := t6_790jobs0




def t6_791root : Job := ⟨plan7382,[],none,⟨15,10,0⟩⟩
def t6_791jobs0 : List Job := [⟨plan7382,[],none,⟨15,10,0⟩⟩]

def t6_791jobs : List Job := t6_791jobs0




def t6_792root : Job := ⟨plan7383,[],none,⟨15,10,0⟩⟩
def t6_792jobs0 : List Job := [⟨plan3478,[⟨2,0,5⟩,⟨9,0,4⟩],(some ⟨9,0,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3478,[⟨2,0,5⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3478,[⟨2,0,5⟩,⟨9,1,4⟩],(some ⟨9,1,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3478,[⟨2,0,5⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨13,8,(-5)⟩⟩,⟨plan3478,[⟨2,0,5⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3478,[⟨2,1,4⟩,⟨9,0,4⟩],(some ⟨9,0,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3478,[⟨2,1,4⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3478,[⟨2,1,4⟩,⟨9,1,4⟩],(some ⟨9,1,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3478,[⟨2,1,4⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨12,8,(-4)⟩⟩,⟨plan3478,[⟨2,1,4⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3478,[⟨2,2,3⟩,⟨9,0,4⟩],(some ⟨9,0,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3478,[⟨2,2,3⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3478,[⟨2,2,3⟩,⟨9,1,4⟩],(some ⟨9,1,4⟩),⟨12,6,(-6)⟩⟩]

def t6_792jobs1 : List Job := [⟨plan3478,[⟨2,2,3⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨11,8,(-3)⟩⟩,⟨plan3478,[⟨2,2,3⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨11,7,(-4)⟩⟩]

def t6_792jobs : List Job := t6_792jobs0++t6_792jobs1



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


