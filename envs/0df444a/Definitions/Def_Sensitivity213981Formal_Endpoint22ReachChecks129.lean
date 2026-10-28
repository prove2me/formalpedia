-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks129
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks129
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:29:16.292966+00:00
-- url     : https://prove2.me/theorems/6d9020ab-fe7c-44a5-a2b8-31aeea30cfd7
-- title:
--   Endpoint22 Reach Checks129 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks129 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_1210jobs2`, `ThreeBoundEndpoint22Reachable.t6_1210jobs3`, `ThreeBoundEndpoint22Reachable.t6_1210jobs4`, `ThreeBoundEndpoint22Reachable.t6_1210jobs`, `ThreeBoundEndpoint22Reachable.t6_1205jobs1`, `ThreeBoundEndpoint22Reachable.t6_1205jobs2`, `ThreeBoundEndpoint22Reachable.t6_1205jobs3`, `ThreeBoundEndpoint22Reachable.t6_1205jobs4`, `ThreeBoundEndpoint22Reachable.t6_1205jobs5`, `ThreeBoundEndpoint22Reachable.t6_1205jobs`, `ThreeBoundEndpoint22Reachable.t6_1205root`, `ThreeBoundEndpoint22Reachable.t6_1206root`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks129.lean, lines 1–100.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans073
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans078
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

def t6_1205root : Job := ⟨plan7051,[],none,⟨15,6,0⟩⟩
def t6_1205jobs0 : List Job := [⟨plan3368,[⟨5,0,3⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨15,3,(-7)⟩⟩,⟨plan3368,[⟨5,0,3⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3368,[⟨5,0,3⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨14,3,(-7)⟩⟩,⟨plan3368,[⟨5,0,3⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨13,3,(-5)⟩⟩,⟨plan3368,[⟨5,0,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨13,3,(-6)⟩⟩,⟨plan3368,[⟨5,0,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨12,3,(-4)⟩⟩,⟨plan3368,[⟨5,0,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨12,3,(-5)⟩⟩,⟨plan3368,[⟨5,1,2⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨14,4,(-5)⟩⟩,⟨plan3368,[⟨5,1,2⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨13,4,(-4)⟩⟩,⟨plan3368,[⟨5,1,2⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨13,4,(-5)⟩⟩,⟨plan3368,[⟨5,1,2⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨12,4,(-3)⟩⟩,⟨plan3368,[⟨5,1,2⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,4,(-4)⟩⟩,⟨plan3368,[⟨5,1,2⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨11,4,(-2)⟩⟩,⟨plan3368,[⟨5,1,2⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,4,(-3)⟩⟩,⟨plan3368,[⟨5,1,3⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨14,3,(-6)⟩⟩,⟨plan3368,[⟨5,1,3⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3368,[⟨5,1,3⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨13,3,(-6)⟩⟩]

def t6_1205jobs1 : List Job := [⟨plan3368,[⟨5,1,3⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨12,3,(-4)⟩⟩,⟨plan3368,[⟨5,1,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,3,(-5)⟩⟩,⟨plan3368,[⟨5,1,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨11,3,(-3)⟩⟩,⟨plan3368,[⟨5,1,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,3,(-4)⟩⟩,⟨plan3368,[⟨5,2,1⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨13,5,(-3)⟩⟩,⟨plan3368,[⟨5,2,1⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨12,5,(-2)⟩⟩,⟨plan3368,[⟨5,2,1⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨12,5,(-3)⟩⟩]

def t6_1205jobs2 : List Job := [⟨plan3368,[⟨5,2,1⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨11,5,(-1)⟩⟩,⟨plan3368,[⟨5,2,1⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨11,5,(-2)⟩⟩,⟨plan3368,[⟨5,2,1⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨10,5,0⟩⟩,⟨plan3368,[⟨5,2,1⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨10,5,(-1)⟩⟩,⟨plan3368,[⟨5,2,2⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨13,4,(-4)⟩⟩]

def t6_1205jobs3 : List Job := [⟨plan3368,[⟨5,2,2⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨12,4,(-3)⟩⟩,⟨plan3368,[⟨5,2,2⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨12,4,(-4)⟩⟩,⟨plan3368,[⟨5,2,2⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨11,4,(-2)⟩⟩,⟨plan3368,[⟨5,2,2⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨11,4,(-3)⟩⟩]

def t6_1205jobs4 : List Job := [⟨plan3368,[⟨5,2,2⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨10,4,(-1)⟩⟩,⟨plan3368,[⟨5,2,2⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨10,4,(-2)⟩⟩,⟨plan3368,[⟨5,2,3⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨13,3,(-5)⟩⟩,⟨plan3368,[⟨5,2,3⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨12,3,(-4)⟩⟩,⟨plan3368,[⟨5,2,3⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨12,3,(-5)⟩⟩]

def t6_1205jobs5 : List Job := [⟨plan3368,[⟨5,2,3⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨11,3,(-3)⟩⟩,⟨plan3368,[⟨5,2,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨11,3,(-4)⟩⟩,⟨plan3368,[⟨5,2,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨10,3,(-2)⟩⟩,⟨plan3368,[⟨5,2,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨10,3,(-3)⟩⟩]

def t6_1205jobs : List Job := t6_1205jobs0++t6_1205jobs1++t6_1205jobs2++t6_1205jobs3++t6_1205jobs4++t6_1205jobs5




def t6_1206root : Job := ⟨plan7052,[],none,⟨15,6,0⟩⟩
def t6_1206jobs0 : List Job := [⟨plan5631,[⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5631,[⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨14,4,(-1)⟩⟩,⟨plan5631,[⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨14,3,(-2)⟩⟩,⟨plan5631,[⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨13,5,1⟩⟩,⟨plan5631,[⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨13,4,0⟩⟩]

def t6_1206jobs1 : List Job := [⟨plan5631,[⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨13,3,(-1)⟩⟩]

def t6_1206jobs : List Job := t6_1206jobs0++t6_1206jobs1




def t6_1207root : Job := ⟨plan7530,[],none,⟨15,10,0⟩⟩
def t6_1207jobs0 : List Job := [⟨plan7530,[],none,⟨15,10,0⟩⟩]

def t6_1207jobs : List Job := t6_1207jobs0




def t6_1208root : Job := ⟨plan7531,[],none,⟨15,10,0⟩⟩
def t6_1208jobs0 : List Job := [⟨plan5771,[⟨5,0,4⟩],(some ⟨5,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5771,[⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨14,7,(-2)⟩⟩,⟨plan5771,[⟨5,1,4⟩],(some ⟨5,1,4⟩),⟨14,6,(-3)⟩⟩]

def t6_1208jobs1 : List Job := [⟨plan5771,[⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨13,8,0⟩⟩,⟨plan5771,[⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨13,7,(-1)⟩⟩]

def t6_1208jobs : List Job := t6_1208jobs0++t6_1208jobs1




def t6_1209root : Job := ⟨plan7532,[],none,⟨15,10,0⟩⟩
def t6_1209jobs0 : List Job := [⟨plan7532,[],none,⟨15,10,0⟩⟩]

def t6_1209jobs : List Job := t6_1209jobs0




def t6_1210root : Job := ⟨plan7533,[],none,⟨15,10,0⟩⟩
def t6_1210jobs0 : List Job := [⟨plan3478,[⟨5,0,4⟩,⟨3,0,5⟩],(some ⟨3,0,5⟩),⟨15,6,(-9)⟩⟩,⟨plan3478,[⟨5,0,4⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3478,[⟨5,0,4⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨13,6,(-7)⟩⟩,⟨plan3478,[⟨5,0,4⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨12,6,(-6)⟩⟩,⟨plan3478,[⟨5,1,3⟩,⟨3,0,5⟩],(some ⟨3,0,5⟩),⟨14,7,(-7)⟩⟩,⟨plan3478,[⟨5,1,3⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨13,7,(-6)⟩⟩,⟨plan3478,[⟨5,1,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3478,[⟨5,1,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,7,(-4)⟩⟩,⟨plan3478,[⟨5,1,4⟩,⟨3,0,5⟩],(some ⟨3,0,5⟩),⟨14,6,(-8)⟩⟩]

def t6_1210jobs1 : List Job := [⟨plan3478,[⟨5,1,4⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3478,[⟨5,1,4⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,6,(-6)⟩⟩,⟨plan3478,[⟨5,1,4⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,6,(-5)⟩⟩,⟨plan3478,[⟨5,2,2⟩,⟨3,0,5⟩],(some ⟨3,0,5⟩),⟨13,8,(-5)⟩⟩,⟨plan3478,[⟨5,2,2⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨12,8,(-4)⟩⟩]

def t6_1210jobs2 : List Job := [⟨plan3478,[⟨5,2,2⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨11,8,(-3)⟩⟩,⟨plan3478,[⟨5,2,2⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨10,8,(-2)⟩⟩,⟨plan3478,[⟨5,2,3⟩,⟨3,0,5⟩],(some ⟨3,0,5⟩),⟨13,7,(-6)⟩⟩]

def t6_1210jobs3 : List Job := [⟨plan3478,[⟨5,2,3⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨12,7,(-5)⟩⟩,⟨plan3478,[⟨5,2,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨11,7,(-4)⟩⟩]

def t6_1210jobs4 : List Job := [⟨plan3478,[⟨5,2,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨10,7,(-3)⟩⟩]

def t6_1210jobs : List Job := t6_1210jobs0++t6_1210jobs1++t6_1210jobs2++t6_1210jobs3++t6_1210jobs4



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


