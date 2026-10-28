-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks082
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks082
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:27:42.948243+00:00
-- url     : https://prove2.me/theorems/3377d111-c60a-420c-b7c0-479efb1b7339
-- title:
--   Endpoint22 Reach Checks082 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks082 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_676root`, `ThreeBoundEndpoint22Reachable.t6_676jobs0`, `ThreeBoundEndpoint22Reachable.t6_676jobs`, `ThreeBoundEndpoint22Reachable.t6_673jobs1`, `ThreeBoundEndpoint22Reachable.t6_673jobs2`, `ThreeBoundEndpoint22Reachable.t6_673jobs3`, `ThreeBoundEndpoint22Reachable.t6_673jobs4`, `ThreeBoundEndpoint22Reachable.t6_673jobs5`, `ThreeBoundEndpoint22Reachable.t6_673jobs6`, `ThreeBoundEndpoint22Reachable.t6_673jobs`, `ThreeBoundEndpoint22Reachable.t6_673root`, `ThreeBoundEndpoint22Reachable.t6_674root`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks082.lean, lines 1–82.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans068
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans072
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

def t6_673root : Job := ⟨plan6590,[],none,⟨15,3,0⟩⟩
def t6_673jobs0 : List Job := [⟨plan3309,[⟨2,0,3⟩,⟨5,0,2⟩],(some ⟨5,0,2⟩),⟨15,1,(-5)⟩⟩,⟨plan3309,[⟨2,0,3⟩,⟨5,1,1⟩],(some ⟨5,1,1⟩),⟨14,2,(-3)⟩⟩,⟨plan3309,[⟨2,0,3⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨14,1,(-4)⟩⟩,⟨plan3309,[⟨2,0,3⟩,⟨5,2,0⟩],(some ⟨5,2,0⟩),⟨13,3,(-1)⟩⟩,⟨plan3309,[⟨2,0,3⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨13,2,(-2)⟩⟩,⟨plan3309,[⟨2,0,3⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨13,1,(-3)⟩⟩,⟨plan3309,[⟨2,1,2⟩,⟨5,0,2⟩],(some ⟨5,0,2⟩),⟨14,1,(-4)⟩⟩,⟨plan3309,[⟨2,1,2⟩,⟨5,1,1⟩],(some ⟨5,1,1⟩),⟨13,2,(-2)⟩⟩,⟨plan3309,[⟨2,1,2⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨13,1,(-3)⟩⟩,⟨plan3309,[⟨2,1,2⟩,⟨5,2,0⟩],(some ⟨5,2,0⟩),⟨12,3,0⟩⟩,⟨plan3309,[⟨2,1,2⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨12,2,(-1)⟩⟩,⟨plan3309,[⟨2,1,2⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨12,1,(-2)⟩⟩,⟨plan3309,[⟨2,1,3⟩,⟨5,0,2⟩],(some ⟨5,0,2⟩),⟨14,1,(-5)⟩⟩,⟨plan3309,[⟨2,1,3⟩,⟨5,1,1⟩],(some ⟨5,1,1⟩),⟨13,2,(-3)⟩⟩]

def t6_673jobs1 : List Job := [⟨plan3309,[⟨2,1,3⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨13,1,(-4)⟩⟩,⟨plan3309,[⟨2,1,3⟩,⟨5,2,0⟩],(some ⟨5,2,0⟩),⟨12,3,(-1)⟩⟩,⟨plan3309,[⟨2,1,3⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨12,2,(-2)⟩⟩,⟨plan3309,[⟨2,1,3⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨12,1,(-3)⟩⟩,⟨plan3309,[⟨2,2,1⟩,⟨5,0,2⟩],(some ⟨5,0,2⟩),⟨13,1,(-3)⟩⟩,⟨plan3309,[⟨2,2,1⟩,⟨5,1,1⟩],(some ⟨5,1,1⟩),⟨12,2,(-1)⟩⟩]

def t6_673jobs2 : List Job := [⟨plan3309,[⟨2,2,1⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨12,1,(-2)⟩⟩,⟨plan3309,[⟨2,2,1⟩,⟨5,2,0⟩],(some ⟨5,2,0⟩),⟨11,3,1⟩⟩,⟨plan3309,[⟨2,2,1⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨11,2,0⟩⟩,⟨plan3309,[⟨2,2,1⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨11,1,(-1)⟩⟩,⟨plan3309,[⟨2,2,2⟩,⟨5,0,2⟩],(some ⟨5,0,2⟩),⟨13,1,(-4)⟩⟩]

def t6_673jobs3 : List Job := [⟨plan3309,[⟨2,2,2⟩,⟨5,1,1⟩],(some ⟨5,1,1⟩),⟨12,2,(-2)⟩⟩,⟨plan3309,[⟨2,2,2⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨12,1,(-3)⟩⟩,⟨plan3309,[⟨2,2,2⟩,⟨5,2,0⟩],(some ⟨5,2,0⟩),⟨11,3,0⟩⟩]

def t6_673jobs4 : List Job := [⟨plan3309,[⟨2,2,2⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨11,2,(-1)⟩⟩,⟨plan3309,[⟨2,2,2⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨11,1,(-2)⟩⟩,⟨plan3309,[⟨2,2,3⟩,⟨5,0,2⟩],(some ⟨5,0,2⟩),⟨13,1,(-5)⟩⟩]

def t6_673jobs5 : List Job := [⟨plan3309,[⟨2,2,3⟩,⟨5,1,1⟩],(some ⟨5,1,1⟩),⟨12,2,(-3)⟩⟩,⟨plan3309,[⟨2,2,3⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨12,1,(-4)⟩⟩,⟨plan3309,[⟨2,2,3⟩,⟨5,2,0⟩],(some ⟨5,2,0⟩),⟨11,3,(-1)⟩⟩,⟨plan3309,[⟨2,2,3⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨11,2,(-2)⟩⟩]

def t6_673jobs6 : List Job := [⟨plan3309,[⟨2,2,3⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨11,1,(-3)⟩⟩]

def t6_673jobs : List Job := t6_673jobs0++t6_673jobs1++t6_673jobs2++t6_673jobs3++t6_673jobs4++t6_673jobs5++t6_673jobs6




def t6_674root : Job := ⟨plan6591,[],none,⟨15,3,0⟩⟩
def t6_674jobs0 : List Job := [⟨plan3310,[⟨2,0,3⟩,⟨5,0,2⟩],(some ⟨5,0,2⟩),⟨15,1,(-5)⟩⟩,⟨plan3310,[⟨2,0,3⟩,⟨5,1,1⟩],(some ⟨5,1,1⟩),⟨14,2,(-3)⟩⟩,⟨plan3310,[⟨2,0,3⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨14,1,(-4)⟩⟩,⟨plan3310,[⟨2,0,3⟩,⟨5,2,0⟩],(some ⟨5,2,0⟩),⟨13,3,(-1)⟩⟩,⟨plan3310,[⟨2,0,3⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨13,2,(-2)⟩⟩,⟨plan3310,[⟨2,0,3⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨13,1,(-3)⟩⟩,⟨plan3310,[⟨2,1,2⟩,⟨5,0,2⟩],(some ⟨5,0,2⟩),⟨14,1,(-4)⟩⟩,⟨plan3310,[⟨2,1,2⟩,⟨5,1,1⟩],(some ⟨5,1,1⟩),⟨13,2,(-2)⟩⟩,⟨plan3310,[⟨2,1,2⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨13,1,(-3)⟩⟩,⟨plan3310,[⟨2,1,2⟩,⟨5,2,0⟩],(some ⟨5,2,0⟩),⟨12,3,0⟩⟩,⟨plan3310,[⟨2,1,2⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨12,2,(-1)⟩⟩,⟨plan3310,[⟨2,1,2⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨12,1,(-2)⟩⟩,⟨plan3310,[⟨2,1,3⟩,⟨5,0,2⟩],(some ⟨5,0,2⟩),⟨14,1,(-5)⟩⟩,⟨plan3310,[⟨2,1,3⟩,⟨5,1,1⟩],(some ⟨5,1,1⟩),⟨13,2,(-3)⟩⟩,⟨plan3310,[⟨2,1,3⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨13,1,(-4)⟩⟩,⟨plan3310,[⟨2,1,3⟩,⟨5,2,0⟩],(some ⟨5,2,0⟩),⟨12,3,(-1)⟩⟩]

def t6_674jobs1 : List Job := [⟨plan3310,[⟨2,1,3⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨12,2,(-2)⟩⟩,⟨plan3310,[⟨2,1,3⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨12,1,(-3)⟩⟩,⟨plan3310,[⟨2,2,1⟩,⟨5,0,2⟩],(some ⟨5,0,2⟩),⟨13,1,(-3)⟩⟩,⟨plan3310,[⟨2,2,1⟩,⟨5,1,1⟩],(some ⟨5,1,1⟩),⟨12,2,(-1)⟩⟩,⟨plan3310,[⟨2,2,1⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨12,1,(-2)⟩⟩]

def t6_674jobs2 : List Job := [⟨plan3310,[⟨2,2,1⟩,⟨5,2,0⟩],(some ⟨5,2,0⟩),⟨11,3,1⟩⟩,⟨plan3310,[⟨2,2,1⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨11,2,0⟩⟩,⟨plan3310,[⟨2,2,1⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨11,1,(-1)⟩⟩,⟨plan3310,[⟨2,2,2⟩,⟨5,0,2⟩],(some ⟨5,0,2⟩),⟨13,1,(-4)⟩⟩]

def t6_674jobs3 : List Job := [⟨plan3310,[⟨2,2,2⟩,⟨5,1,1⟩],(some ⟨5,1,1⟩),⟨12,2,(-2)⟩⟩,⟨plan3310,[⟨2,2,2⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨12,1,(-3)⟩⟩,⟨plan3310,[⟨2,2,2⟩,⟨5,2,0⟩],(some ⟨5,2,0⟩),⟨11,3,0⟩⟩]

def t6_674jobs4 : List Job := [⟨plan3310,[⟨2,2,2⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨11,2,(-1)⟩⟩]

def t6_674jobs5 : List Job := [⟨plan3310,[⟨2,2,2⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨11,1,(-2)⟩⟩,⟨plan3310,[⟨2,2,3⟩,⟨5,0,2⟩],(some ⟨5,0,2⟩),⟨13,1,(-5)⟩⟩,⟨plan3310,[⟨2,2,3⟩,⟨5,1,1⟩],(some ⟨5,1,1⟩),⟨12,2,(-3)⟩⟩,⟨plan3310,[⟨2,2,3⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨12,1,(-4)⟩⟩]

def t6_674jobs6 : List Job := [⟨plan3310,[⟨2,2,3⟩,⟨5,2,0⟩],(some ⟨5,2,0⟩),⟨11,3,(-1)⟩⟩,⟨plan3310,[⟨2,2,3⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨11,2,(-2)⟩⟩,⟨plan3310,[⟨2,2,3⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨11,1,(-3)⟩⟩]

def t6_674jobs : List Job := t6_674jobs0++t6_674jobs1++t6_674jobs2++t6_674jobs3++t6_674jobs4++t6_674jobs5++t6_674jobs6




def t6_675root : Job := ⟨plan6592,[],none,⟨15,3,0⟩⟩
def t6_675jobs0 : List Job := [⟨plan5509,[⟨2,0,3⟩],(some ⟨2,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5509,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨14,3,(-2)⟩⟩,⟨plan5509,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨14,3,(-3)⟩⟩,⟨plan5509,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨13,3,(-1)⟩⟩,⟨plan5509,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨13,3,(-2)⟩⟩]

def t6_675jobs1 : List Job := [⟨plan5509,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨13,3,(-3)⟩⟩]

def t6_675jobs : List Job := t6_675jobs0++t6_675jobs1




def t6_676root : Job := ⟨plan6929,[],none,⟨15,6,0⟩⟩
def t6_676jobs0 : List Job := [⟨plan6929,[],none,⟨15,6,0⟩⟩]

def t6_676jobs : List Job := t6_676jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


