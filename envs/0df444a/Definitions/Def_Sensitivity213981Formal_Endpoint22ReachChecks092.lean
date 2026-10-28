-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks092
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks092
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:28:21.913831+00:00
-- url     : https://prove2.me/theorems/a49246b6-8fe2-45f0-834c-11442c38a7f0
-- title:
--   Endpoint22 Reach Checks092 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks092 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_779root`, `ThreeBoundEndpoint22Reachable.t6_779jobs0`, `ThreeBoundEndpoint22Reachable.t6_779jobs`, `ThreeBoundEndpoint22Reachable.t6_776jobs1`, `ThreeBoundEndpoint22Reachable.t6_776jobs2`, `ThreeBoundEndpoint22Reachable.t6_776jobs3`, `ThreeBoundEndpoint22Reachable.t6_776jobs4`, `ThreeBoundEndpoint22Reachable.t6_776jobs5`, `ThreeBoundEndpoint22Reachable.t6_776jobs6`, `ThreeBoundEndpoint22Reachable.t6_776jobs`, `ThreeBoundEndpoint22Reachable.t6_776root`, `ThreeBoundEndpoint22Reachable.t6_777root`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks092.lean, lines 1–82.

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

def t6_776root : Job := ⟨plan6602,[],none,⟨15,3,0⟩⟩
def t6_776jobs0 : List Job := [⟨plan3309,[⟨2,0,3⟩,⟨9,0,2⟩],(some ⟨9,0,2⟩),⟨15,1,(-5)⟩⟩,⟨plan3309,[⟨2,0,3⟩,⟨9,1,1⟩],(some ⟨9,1,1⟩),⟨14,2,(-3)⟩⟩,⟨plan3309,[⟨2,0,3⟩,⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨14,1,(-4)⟩⟩,⟨plan3309,[⟨2,0,3⟩,⟨9,2,0⟩],(some ⟨9,2,0⟩),⟨13,3,(-1)⟩⟩,⟨plan3309,[⟨2,0,3⟩,⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨13,2,(-2)⟩⟩,⟨plan3309,[⟨2,0,3⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨13,1,(-3)⟩⟩,⟨plan3309,[⟨2,1,2⟩,⟨9,0,2⟩],(some ⟨9,0,2⟩),⟨14,1,(-4)⟩⟩,⟨plan3309,[⟨2,1,2⟩,⟨9,1,1⟩],(some ⟨9,1,1⟩),⟨13,2,(-2)⟩⟩,⟨plan3309,[⟨2,1,2⟩,⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨13,1,(-3)⟩⟩,⟨plan3309,[⟨2,1,2⟩,⟨9,2,0⟩],(some ⟨9,2,0⟩),⟨12,3,0⟩⟩,⟨plan3309,[⟨2,1,2⟩,⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨12,2,(-1)⟩⟩,⟨plan3309,[⟨2,1,2⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨12,1,(-2)⟩⟩,⟨plan3309,[⟨2,1,3⟩,⟨9,0,2⟩],(some ⟨9,0,2⟩),⟨14,1,(-5)⟩⟩,⟨plan3309,[⟨2,1,3⟩,⟨9,1,1⟩],(some ⟨9,1,1⟩),⟨13,2,(-3)⟩⟩]

def t6_776jobs1 : List Job := [⟨plan3309,[⟨2,1,3⟩,⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨13,1,(-4)⟩⟩,⟨plan3309,[⟨2,1,3⟩,⟨9,2,0⟩],(some ⟨9,2,0⟩),⟨12,3,(-1)⟩⟩,⟨plan3309,[⟨2,1,3⟩,⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨12,2,(-2)⟩⟩,⟨plan3309,[⟨2,1,3⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨12,1,(-3)⟩⟩,⟨plan3309,[⟨2,2,1⟩,⟨9,0,2⟩],(some ⟨9,0,2⟩),⟨13,1,(-3)⟩⟩,⟨plan3309,[⟨2,2,1⟩,⟨9,1,1⟩],(some ⟨9,1,1⟩),⟨12,2,(-1)⟩⟩]

def t6_776jobs2 : List Job := [⟨plan3309,[⟨2,2,1⟩,⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨12,1,(-2)⟩⟩,⟨plan3309,[⟨2,2,1⟩,⟨9,2,0⟩],(some ⟨9,2,0⟩),⟨11,3,1⟩⟩,⟨plan3309,[⟨2,2,1⟩,⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨11,2,0⟩⟩,⟨plan3309,[⟨2,2,1⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨11,1,(-1)⟩⟩,⟨plan3309,[⟨2,2,2⟩,⟨9,0,2⟩],(some ⟨9,0,2⟩),⟨13,1,(-4)⟩⟩]

def t6_776jobs3 : List Job := [⟨plan3309,[⟨2,2,2⟩,⟨9,1,1⟩],(some ⟨9,1,1⟩),⟨12,2,(-2)⟩⟩,⟨plan3309,[⟨2,2,2⟩,⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨12,1,(-3)⟩⟩,⟨plan3309,[⟨2,2,2⟩,⟨9,2,0⟩],(some ⟨9,2,0⟩),⟨11,3,0⟩⟩]

def t6_776jobs4 : List Job := [⟨plan3309,[⟨2,2,2⟩,⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨11,2,(-1)⟩⟩,⟨plan3309,[⟨2,2,2⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨11,1,(-2)⟩⟩,⟨plan3309,[⟨2,2,3⟩,⟨9,0,2⟩],(some ⟨9,0,2⟩),⟨13,1,(-5)⟩⟩]

def t6_776jobs5 : List Job := [⟨plan3309,[⟨2,2,3⟩,⟨9,1,1⟩],(some ⟨9,1,1⟩),⟨12,2,(-3)⟩⟩,⟨plan3309,[⟨2,2,3⟩,⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨12,1,(-4)⟩⟩,⟨plan3309,[⟨2,2,3⟩,⟨9,2,0⟩],(some ⟨9,2,0⟩),⟨11,3,(-1)⟩⟩,⟨plan3309,[⟨2,2,3⟩,⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨11,2,(-2)⟩⟩]

def t6_776jobs6 : List Job := [⟨plan3309,[⟨2,2,3⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨11,1,(-3)⟩⟩]

def t6_776jobs : List Job := t6_776jobs0++t6_776jobs1++t6_776jobs2++t6_776jobs3++t6_776jobs4++t6_776jobs5++t6_776jobs6




def t6_777root : Job := ⟨plan6603,[],none,⟨15,3,0⟩⟩
def t6_777jobs0 : List Job := [⟨plan3310,[⟨2,0,3⟩,⟨9,0,2⟩],(some ⟨9,0,2⟩),⟨15,1,(-5)⟩⟩,⟨plan3310,[⟨2,0,3⟩,⟨9,1,1⟩],(some ⟨9,1,1⟩),⟨14,2,(-3)⟩⟩,⟨plan3310,[⟨2,0,3⟩,⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨14,1,(-4)⟩⟩,⟨plan3310,[⟨2,0,3⟩,⟨9,2,0⟩],(some ⟨9,2,0⟩),⟨13,3,(-1)⟩⟩,⟨plan3310,[⟨2,0,3⟩,⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨13,2,(-2)⟩⟩,⟨plan3310,[⟨2,0,3⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨13,1,(-3)⟩⟩,⟨plan3310,[⟨2,1,2⟩,⟨9,0,2⟩],(some ⟨9,0,2⟩),⟨14,1,(-4)⟩⟩,⟨plan3310,[⟨2,1,2⟩,⟨9,1,1⟩],(some ⟨9,1,1⟩),⟨13,2,(-2)⟩⟩,⟨plan3310,[⟨2,1,2⟩,⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨13,1,(-3)⟩⟩,⟨plan3310,[⟨2,1,2⟩,⟨9,2,0⟩],(some ⟨9,2,0⟩),⟨12,3,0⟩⟩,⟨plan3310,[⟨2,1,2⟩,⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨12,2,(-1)⟩⟩,⟨plan3310,[⟨2,1,2⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨12,1,(-2)⟩⟩,⟨plan3310,[⟨2,1,3⟩,⟨9,0,2⟩],(some ⟨9,0,2⟩),⟨14,1,(-5)⟩⟩,⟨plan3310,[⟨2,1,3⟩,⟨9,1,1⟩],(some ⟨9,1,1⟩),⟨13,2,(-3)⟩⟩,⟨plan3310,[⟨2,1,3⟩,⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨13,1,(-4)⟩⟩,⟨plan3310,[⟨2,1,3⟩,⟨9,2,0⟩],(some ⟨9,2,0⟩),⟨12,3,(-1)⟩⟩]

def t6_777jobs1 : List Job := [⟨plan3310,[⟨2,1,3⟩,⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨12,2,(-2)⟩⟩,⟨plan3310,[⟨2,1,3⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨12,1,(-3)⟩⟩,⟨plan3310,[⟨2,2,1⟩,⟨9,0,2⟩],(some ⟨9,0,2⟩),⟨13,1,(-3)⟩⟩,⟨plan3310,[⟨2,2,1⟩,⟨9,1,1⟩],(some ⟨9,1,1⟩),⟨12,2,(-1)⟩⟩,⟨plan3310,[⟨2,2,1⟩,⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨12,1,(-2)⟩⟩]

def t6_777jobs2 : List Job := [⟨plan3310,[⟨2,2,1⟩,⟨9,2,0⟩],(some ⟨9,2,0⟩),⟨11,3,1⟩⟩,⟨plan3310,[⟨2,2,1⟩,⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨11,2,0⟩⟩,⟨plan3310,[⟨2,2,1⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨11,1,(-1)⟩⟩,⟨plan3310,[⟨2,2,2⟩,⟨9,0,2⟩],(some ⟨9,0,2⟩),⟨13,1,(-4)⟩⟩]

def t6_777jobs3 : List Job := [⟨plan3310,[⟨2,2,2⟩,⟨9,1,1⟩],(some ⟨9,1,1⟩),⟨12,2,(-2)⟩⟩,⟨plan3310,[⟨2,2,2⟩,⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨12,1,(-3)⟩⟩,⟨plan3310,[⟨2,2,2⟩,⟨9,2,0⟩],(some ⟨9,2,0⟩),⟨11,3,0⟩⟩]

def t6_777jobs4 : List Job := [⟨plan3310,[⟨2,2,2⟩,⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨11,2,(-1)⟩⟩]

def t6_777jobs5 : List Job := [⟨plan3310,[⟨2,2,2⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨11,1,(-2)⟩⟩,⟨plan3310,[⟨2,2,3⟩,⟨9,0,2⟩],(some ⟨9,0,2⟩),⟨13,1,(-5)⟩⟩,⟨plan3310,[⟨2,2,3⟩,⟨9,1,1⟩],(some ⟨9,1,1⟩),⟨12,2,(-3)⟩⟩,⟨plan3310,[⟨2,2,3⟩,⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨12,1,(-4)⟩⟩]

def t6_777jobs6 : List Job := [⟨plan3310,[⟨2,2,3⟩,⟨9,2,0⟩],(some ⟨9,2,0⟩),⟨11,3,(-1)⟩⟩,⟨plan3310,[⟨2,2,3⟩,⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨11,2,(-2)⟩⟩,⟨plan3310,[⟨2,2,3⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨11,1,(-3)⟩⟩]

def t6_777jobs : List Job := t6_777jobs0++t6_777jobs1++t6_777jobs2++t6_777jobs3++t6_777jobs4++t6_777jobs5++t6_777jobs6




def t6_778root : Job := ⟨plan6604,[],none,⟨15,3,0⟩⟩
def t6_778jobs0 : List Job := [⟨plan5531,[⟨2,0,3⟩],(some ⟨2,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5531,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨14,3,(-2)⟩⟩,⟨plan5531,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨14,3,(-3)⟩⟩,⟨plan5531,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨13,3,(-1)⟩⟩,⟨plan5531,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨13,3,(-2)⟩⟩]

def t6_778jobs1 : List Job := [⟨plan5531,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨13,3,(-3)⟩⟩]

def t6_778jobs : List Job := t6_778jobs0++t6_778jobs1




def t6_779root : Job := ⟨plan6954,[],none,⟨15,6,0⟩⟩
def t6_779jobs0 : List Job := [⟨plan6954,[],none,⟨15,6,0⟩⟩]

def t6_779jobs : List Job := t6_779jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


