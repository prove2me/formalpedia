-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks087
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks087
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:26:43.251987+00:00
-- url     : https://prove2.me/theorems/d0ba1da9-b579-4a13-a61d-36dedf470129
-- title:
--   Endpoint22 Reach Checks087 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks087 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_726root`, `ThreeBoundEndpoint22Reachable.t6_726jobs0`, `ThreeBoundEndpoint22Reachable.t6_726jobs`, `ThreeBoundEndpoint22Reachable.t6_727root`, `ThreeBoundEndpoint22Reachable.t6_727jobs0`, `ThreeBoundEndpoint22Reachable.t6_727jobs1`, `ThreeBoundEndpoint22Reachable.t6_727jobs2`, `ThreeBoundEndpoint22Reachable.t6_727jobs`, `ThreeBoundEndpoint22Reachable.t6_728root`, `ThreeBoundEndpoint22Reachable.t6_728jobs0`, `ThreeBoundEndpoint22Reachable.t6_728jobs`, `ThreeBoundEndpoint22Reachable.t6_720root`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks087.lean, lines 1–170.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans066
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans068
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

def t6_719root : Job := ⟨plan7341,[],none,⟨15,10,0⟩⟩
def t6_719jobs0 : List Job := [⟨plan7341,[],none,⟨15,10,0⟩⟩]

def t6_719jobs : List Job := t6_719jobs0




def t6_720root : Job := ⟨plan7342,[],none,⟨15,10,0⟩⟩
def t6_720jobs0 : List Job := [⟨plan3481,[⟨2,0,5⟩,⟨5,0,4⟩],(some ⟨5,0,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3481,[⟨2,0,5⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3481,[⟨2,0,5⟩,⟨5,1,4⟩],(some ⟨5,1,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3481,[⟨2,0,5⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨13,8,(-5)⟩⟩,⟨plan3481,[⟨2,0,5⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3481,[⟨2,1,4⟩,⟨5,0,4⟩],(some ⟨5,0,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3481,[⟨2,1,4⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3481,[⟨2,1,4⟩,⟨5,1,4⟩],(some ⟨5,1,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3481,[⟨2,1,4⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨12,8,(-4)⟩⟩,⟨plan3481,[⟨2,1,4⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3481,[⟨2,2,3⟩,⟨5,0,4⟩],(some ⟨5,0,4⟩),⟨13,6,(-7)⟩⟩]

def t6_720jobs1 : List Job := [⟨plan3481,[⟨2,2,3⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3481,[⟨2,2,3⟩,⟨5,1,4⟩],(some ⟨5,1,4⟩),⟨12,6,(-6)⟩⟩,⟨plan3481,[⟨2,2,3⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨11,8,(-3)⟩⟩]

def t6_720jobs2 : List Job := [⟨plan3481,[⟨2,2,3⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨11,7,(-4)⟩⟩]

def t6_720jobs : List Job := t6_720jobs0++t6_720jobs1++t6_720jobs2




def t6_721root : Job := ⟨plan7343,[],none,⟨15,10,0⟩⟩
def t6_721jobs0 : List Job := [⟨plan3482,[⟨2,0,5⟩,⟨5,0,4⟩],(some ⟨5,0,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3482,[⟨2,0,5⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3482,[⟨2,0,5⟩,⟨5,1,4⟩],(some ⟨5,1,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3482,[⟨2,0,5⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨13,8,(-5)⟩⟩,⟨plan3482,[⟨2,0,5⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3482,[⟨2,1,4⟩,⟨5,0,4⟩],(some ⟨5,0,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3482,[⟨2,1,4⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3482,[⟨2,1,4⟩,⟨5,1,4⟩],(some ⟨5,1,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3482,[⟨2,1,4⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨12,8,(-4)⟩⟩,⟨plan3482,[⟨2,1,4⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3482,[⟨2,2,3⟩,⟨5,0,4⟩],(some ⟨5,0,4⟩),⟨13,6,(-7)⟩⟩]

def t6_721jobs1 : List Job := [⟨plan3482,[⟨2,2,3⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3482,[⟨2,2,3⟩,⟨5,1,4⟩],(some ⟨5,1,4⟩),⟨12,6,(-6)⟩⟩]

def t6_721jobs2 : List Job := [⟨plan3482,[⟨2,2,3⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨11,8,(-3)⟩⟩]

def t6_721jobs3 : List Job := [⟨plan3482,[⟨2,2,3⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨11,7,(-4)⟩⟩]

def t6_721jobs : List Job := t6_721jobs0++t6_721jobs1++t6_721jobs2++t6_721jobs3




def t6_722root : Job := ⟨plan7344,[],none,⟨15,10,0⟩⟩
def t6_722jobs0 : List Job := [⟨plan3483,[⟨2,0,5⟩,⟨5,0,4⟩],(some ⟨5,0,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3483,[⟨2,0,5⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3483,[⟨2,0,5⟩,⟨5,1,4⟩],(some ⟨5,1,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3483,[⟨2,0,5⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨13,8,(-5)⟩⟩,⟨plan3483,[⟨2,0,5⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3483,[⟨2,1,4⟩,⟨5,0,4⟩],(some ⟨5,0,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3483,[⟨2,1,4⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3483,[⟨2,1,4⟩,⟨5,1,4⟩],(some ⟨5,1,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3483,[⟨2,1,4⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨12,8,(-4)⟩⟩,⟨plan3483,[⟨2,1,4⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3483,[⟨2,2,3⟩,⟨5,0,4⟩],(some ⟨5,0,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3483,[⟨2,2,3⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3483,[⟨2,2,3⟩,⟨5,1,4⟩],(some ⟨5,1,4⟩),⟨12,6,(-6)⟩⟩]

def t6_722jobs1 : List Job := [⟨plan3483,[⟨2,2,3⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨11,8,(-3)⟩⟩,⟨plan3483,[⟨2,2,3⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨11,7,(-4)⟩⟩]

def t6_722jobs : List Job := t6_722jobs0++t6_722jobs1




def t6_723root : Job := ⟨plan7345,[],none,⟨15,10,0⟩⟩
def t6_723jobs0 : List Job := [⟨plan7345,[],none,⟨15,10,0⟩⟩]

def t6_723jobs : List Job := t6_723jobs0




def t6_724root : Job := ⟨plan7346,[],none,⟨15,10,0⟩⟩
def t6_724jobs0 : List Job := [⟨plan5858,[⟨2,0,5⟩],(some ⟨2,0,5⟩),⟨15,10,(-5)⟩⟩,⟨plan5858,[⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨14,10,(-4)⟩⟩]

def t6_724jobs1 : List Job := [⟨plan5858,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨13,10,(-3)⟩⟩]

def t6_724jobs : List Job := t6_724jobs0++t6_724jobs1




def t6_725root : Job := ⟨plan6396,[],none,⟨15,1,0⟩⟩
def t6_725jobs0 : List Job := [⟨plan6396,[],none,⟨15,1,0⟩⟩]

def t6_725jobs : List Job := t6_725jobs0




def t6_726root : Job := ⟨plan6596,[],none,⟨15,3,0⟩⟩
def t6_726jobs0 : List Job := [⟨plan6596,[],none,⟨15,3,0⟩⟩]

def t6_726jobs : List Job := t6_726jobs0




def t6_727root : Job := ⟨plan6597,[],none,⟨15,3,0⟩⟩
def t6_727jobs0 : List Job := [⟨plan5516,[⟨2,0,3⟩],(some ⟨2,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5516,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨14,3,(-2)⟩⟩,⟨plan5516,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨14,3,(-3)⟩⟩,⟨plan5516,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨13,3,(-1)⟩⟩]

def t6_727jobs1 : List Job := [⟨plan5516,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨13,3,(-2)⟩⟩]

def t6_727jobs2 : List Job := [⟨plan5516,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨13,3,(-3)⟩⟩]

def t6_727jobs : List Job := t6_727jobs0++t6_727jobs1++t6_727jobs2




def t6_728root : Job := ⟨plan6598,[],none,⟨15,3,0⟩⟩
def t6_728jobs0 : List Job := [⟨plan6598,[],none,⟨15,3,0⟩⟩]

def t6_728jobs : List Job := t6_728jobs0




def t6_729root : Job := ⟨plan6947,[],none,⟨15,6,0⟩⟩
def t6_729jobs0 : List Job := [⟨plan6947,[],none,⟨15,6,0⟩⟩]

def t6_729jobs : List Job := t6_729jobs0




def t6_730root : Job := ⟨plan6948,[],none,⟨15,6,0⟩⟩
def t6_730jobs0 : List Job := [⟨plan3414,[⟨2,1,3⟩,⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3414,[⟨2,1,3⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨13,4,(-4)⟩⟩,⟨plan3414,[⟨2,1,3⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3414,[⟨2,1,3⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨12,5,(-2)⟩⟩,⟨plan3414,[⟨2,1,3⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨12,4,(-3)⟩⟩,⟨plan3414,[⟨2,1,3⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨12,3,(-4)⟩⟩,⟨plan3414,[⟨2,1,4⟩,⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨14,3,(-7)⟩⟩,⟨plan3414,[⟨2,1,4⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨13,4,(-5)⟩⟩,⟨plan3414,[⟨2,1,4⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨13,3,(-6)⟩⟩,⟨plan3414,[⟨2,1,4⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨12,5,(-3)⟩⟩,⟨plan3414,[⟨2,1,4⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨12,4,(-4)⟩⟩,⟨plan3414,[⟨2,1,4⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨12,3,(-5)⟩⟩,⟨plan3414,[⟨2,2,2⟩,⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3414,[⟨2,2,2⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨12,4,(-3)⟩⟩,⟨plan3414,[⟨2,2,2⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨12,3,(-4)⟩⟩]

def t6_730jobs1 : List Job := [⟨plan3414,[⟨2,2,2⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨11,5,(-1)⟩⟩,⟨plan3414,[⟨2,2,2⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨11,4,(-2)⟩⟩,⟨plan3414,[⟨2,2,2⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨11,3,(-3)⟩⟩,⟨plan3414,[⟨2,2,3⟩,⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨13,3,(-6)⟩⟩]

def t6_730jobs2 : List Job := [⟨plan3414,[⟨2,2,3⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨12,4,(-4)⟩⟩,⟨plan3414,[⟨2,2,3⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨12,3,(-5)⟩⟩,⟨plan3414,[⟨2,2,3⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨11,5,(-2)⟩⟩,⟨plan3414,[⟨2,2,3⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨11,4,(-3)⟩⟩]

def t6_730jobs3 : List Job := [⟨plan3414,[⟨2,2,3⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨11,3,(-4)⟩⟩]

def t6_730jobs : List Job := t6_730jobs0++t6_730jobs1++t6_730jobs2++t6_730jobs3



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


