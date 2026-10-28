-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks097
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks097
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:28:23.85173+00:00
-- url     : https://prove2.me/theorems/6751ac66-5956-4527-a424-ffa1417e83e7
-- title:
--   Endpoint22 Reach Checks097 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks097 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_807jobs2`, `ThreeBoundEndpoint22Reachable.t6_819root`, `ThreeBoundEndpoint22Reachable.t6_819jobs0`, `ThreeBoundEndpoint22Reachable.t6_819jobs`, `ThreeBoundEndpoint22Reachable.t6_820root`, `ThreeBoundEndpoint22Reachable.t6_820jobs0`, `ThreeBoundEndpoint22Reachable.t6_820jobs`, `ThreeBoundEndpoint22Reachable.t6_821root`, `ThreeBoundEndpoint22Reachable.t6_821jobs0`, `ThreeBoundEndpoint22Reachable.t6_821jobs`, `ThreeBoundEndpoint22Reachable.t6_807jobs`, `ThreeBoundEndpoint22Reachable.t6_822root`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks097.lean, lines 1–273.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans072
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans076
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans077
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

def t6_807root : Job := ⟨plan6967,[],none,⟨15,6,0⟩⟩
def t6_807jobs0 : List Job := [⟨plan5736,[⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5736,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨14,6,(-3)⟩⟩,⟨plan5736,[⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨14,6,(-4)⟩⟩]

def t6_807jobs1 : List Job := [⟨plan5736,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨13,6,(-2)⟩⟩]

def t6_807jobs2 : List Job := [⟨plan5736,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨13,6,(-3)⟩⟩]

def t6_807jobs : List Job := t6_807jobs0++t6_807jobs1++t6_807jobs2




def t6_808root : Job := ⟨plan6968,[],none,⟨15,6,0⟩⟩
def t6_808jobs0 : List Job := [⟨plan5737,[⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5737,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨14,6,(-3)⟩⟩,⟨plan5737,[⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨14,6,(-4)⟩⟩]

def t6_808jobs1 : List Job := [⟨plan5737,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨13,6,(-2)⟩⟩]

def t6_808jobs2 : List Job := [⟨plan5737,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨13,6,(-3)⟩⟩]

def t6_808jobs : List Job := t6_808jobs0++t6_808jobs1++t6_808jobs2




def t6_809root : Job := ⟨plan6969,[],none,⟨15,6,0⟩⟩
def t6_809jobs0 : List Job := [⟨plan6969,[],none,⟨15,6,0⟩⟩]

def t6_809jobs : List Job := t6_809jobs0




def t6_810root : Job := ⟨plan7391,[],none,⟨15,10,0⟩⟩
def t6_810jobs0 : List Job := [⟨plan7391,[],none,⟨15,10,0⟩⟩]

def t6_810jobs : List Job := t6_810jobs0




def t6_811root : Job := ⟨plan7392,[],none,⟨15,10,0⟩⟩
def t6_811jobs0 : List Job := [⟨plan7392,[],none,⟨15,10,0⟩⟩]

def t6_811jobs : List Job := t6_811jobs0




def t6_812root : Job := ⟨plan7393,[],none,⟨15,10,0⟩⟩
def t6_812jobs0 : List Job := [⟨plan7393,[],none,⟨15,10,0⟩⟩]

def t6_812jobs : List Job := t6_812jobs0




def t6_813root : Job := ⟨plan7394,[],none,⟨15,10,0⟩⟩
def t6_813jobs0 : List Job := [⟨plan7394,[],none,⟨15,10,0⟩⟩]

def t6_813jobs : List Job := t6_813jobs0




def t6_814root : Job := ⟨plan7395,[],none,⟨15,10,0⟩⟩
def t6_814jobs0 : List Job := [⟨plan7395,[],none,⟨15,10,0⟩⟩]

def t6_814jobs : List Job := t6_814jobs0




def t6_815root : Job := ⟨plan7396,[],none,⟨15,10,0⟩⟩
def t6_815jobs0 : List Job := [⟨plan7396,[],none,⟨15,10,0⟩⟩]

def t6_815jobs : List Job := t6_815jobs0




def t6_816root : Job := ⟨plan7397,[],none,⟨15,10,0⟩⟩
def t6_816jobs0 : List Job := [⟨plan7397,[],none,⟨15,10,0⟩⟩]

def t6_816jobs : List Job := t6_816jobs0




def t6_817root : Job := ⟨plan6970,[],none,⟨15,6,0⟩⟩
def t6_817jobs0 : List Job := [⟨plan6970,[],none,⟨15,6,0⟩⟩]

def t6_817jobs : List Job := t6_817jobs0




def t6_818root : Job := ⟨plan7398,[],none,⟨15,10,0⟩⟩
def t6_818jobs0 : List Job := [⟨plan7398,[],none,⟨15,10,0⟩⟩]

def t6_818jobs : List Job := t6_818jobs0




def t6_819root : Job := ⟨plan7399,[],none,⟨15,10,0⟩⟩
def t6_819jobs0 : List Job := [⟨plan7399,[],none,⟨15,10,0⟩⟩]

def t6_819jobs : List Job := t6_819jobs0




def t6_820root : Job := ⟨plan7400,[],none,⟨15,10,0⟩⟩
def t6_820jobs0 : List Job := [⟨plan7400,[],none,⟨15,10,0⟩⟩]

def t6_820jobs : List Job := t6_820jobs0




def t6_821root : Job := ⟨plan7401,[],none,⟨15,10,0⟩⟩
def t6_821jobs0 : List Job := [⟨plan7401,[],none,⟨15,10,0⟩⟩]

def t6_821jobs : List Job := t6_821jobs0




def t6_822root : Job := ⟨plan7402,[],none,⟨15,10,0⟩⟩
def t6_822jobs0 : List Job := [⟨plan7402,[],none,⟨15,10,0⟩⟩]

def t6_822jobs : List Job := t6_822jobs0




def t6_823root : Job := ⟨plan7403,[],none,⟨15,10,0⟩⟩
def t6_823jobs0 : List Job := [⟨plan7403,[],none,⟨15,10,0⟩⟩]

def t6_823jobs : List Job := t6_823jobs0




def t6_824root : Job := ⟨plan7404,[],none,⟨15,10,0⟩⟩
def t6_824jobs0 : List Job := [⟨plan3507,[⟨2,0,5⟩,⟨9,0,4⟩],(some ⟨9,0,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3507,[⟨2,0,5⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3507,[⟨2,0,5⟩,⟨9,1,4⟩],(some ⟨9,1,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3507,[⟨2,0,5⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨13,8,(-5)⟩⟩,⟨plan3507,[⟨2,0,5⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3507,[⟨2,1,4⟩,⟨9,0,4⟩],(some ⟨9,0,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3507,[⟨2,1,4⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3507,[⟨2,1,4⟩,⟨9,1,4⟩],(some ⟨9,1,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3507,[⟨2,1,4⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨12,8,(-4)⟩⟩,⟨plan3507,[⟨2,1,4⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3507,[⟨2,2,3⟩,⟨9,0,4⟩],(some ⟨9,0,4⟩),⟨13,6,(-7)⟩⟩]

def t6_824jobs1 : List Job := [⟨plan3507,[⟨2,2,3⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3507,[⟨2,2,3⟩,⟨9,1,4⟩],(some ⟨9,1,4⟩),⟨12,6,(-6)⟩⟩,⟨plan3507,[⟨2,2,3⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨11,8,(-3)⟩⟩]

def t6_824jobs2 : List Job := [⟨plan3507,[⟨2,2,3⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨11,7,(-4)⟩⟩]

def t6_824jobs : List Job := t6_824jobs0++t6_824jobs1++t6_824jobs2




def t6_825root : Job := ⟨plan7405,[],none,⟨15,10,0⟩⟩
def t6_825jobs0 : List Job := [⟨plan3508,[⟨2,0,5⟩,⟨9,0,4⟩],(some ⟨9,0,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3508,[⟨2,0,5⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3508,[⟨2,0,5⟩,⟨9,1,4⟩],(some ⟨9,1,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3508,[⟨2,0,5⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨13,8,(-5)⟩⟩,⟨plan3508,[⟨2,0,5⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3508,[⟨2,1,4⟩,⟨9,0,4⟩],(some ⟨9,0,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3508,[⟨2,1,4⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3508,[⟨2,1,4⟩,⟨9,1,4⟩],(some ⟨9,1,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3508,[⟨2,1,4⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨12,8,(-4)⟩⟩,⟨plan3508,[⟨2,1,4⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3508,[⟨2,2,3⟩,⟨9,0,4⟩],(some ⟨9,0,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3508,[⟨2,2,3⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3508,[⟨2,2,3⟩,⟨9,1,4⟩],(some ⟨9,1,4⟩),⟨12,6,(-6)⟩⟩]

def t6_825jobs1 : List Job := [⟨plan3508,[⟨2,2,3⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨11,8,(-3)⟩⟩,⟨plan3508,[⟨2,2,3⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨11,7,(-4)⟩⟩]

def t6_825jobs : List Job := t6_825jobs0++t6_825jobs1




def t6_826root : Job := ⟨plan7406,[],none,⟨15,10,0⟩⟩
def t6_826jobs0 : List Job := [⟨plan7406,[],none,⟨15,10,0⟩⟩]

def t6_826jobs : List Job := t6_826jobs0




def t6_827root : Job := ⟨plan7407,[],none,⟨15,10,0⟩⟩
def t6_827jobs0 : List Job := [⟨plan7407,[],none,⟨15,10,0⟩⟩]

def t6_827jobs : List Job := t6_827jobs0




def t6_828root : Job := ⟨plan7408,[],none,⟨15,10,0⟩⟩
def t6_828jobs0 : List Job := [⟨plan3485,[⟨2,0,5⟩,⟨10,0,4⟩],(some ⟨10,0,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3485,[⟨2,0,5⟩,⟨10,1,3⟩],(some ⟨10,1,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3485,[⟨2,0,5⟩,⟨10,1,4⟩],(some ⟨10,1,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3485,[⟨2,0,5⟩,⟨10,2,2⟩],(some ⟨10,2,2⟩),⟨13,8,(-5)⟩⟩,⟨plan3485,[⟨2,0,5⟩,⟨10,2,3⟩],(some ⟨10,2,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3485,[⟨2,0,5⟩,⟨10,3,1⟩],(some ⟨10,3,1⟩),⟨12,9,(-3)⟩⟩,⟨plan3485,[⟨2,0,5⟩,⟨10,3,2⟩],(some ⟨10,3,2⟩),⟨12,8,(-4)⟩⟩,⟨plan3485,[⟨2,1,4⟩,⟨10,0,4⟩],(some ⟨10,0,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3485,[⟨2,1,4⟩,⟨10,1,3⟩],(some ⟨10,1,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3485,[⟨2,1,4⟩,⟨10,1,4⟩],(some ⟨10,1,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3485,[⟨2,1,4⟩,⟨10,2,2⟩],(some ⟨10,2,2⟩),⟨12,8,(-4)⟩⟩,⟨plan3485,[⟨2,1,4⟩,⟨10,2,3⟩],(some ⟨10,2,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3485,[⟨2,1,4⟩,⟨10,3,1⟩],(some ⟨10,3,1⟩),⟨11,9,(-2)⟩⟩,⟨plan3485,[⟨2,1,4⟩,⟨10,3,2⟩],(some ⟨10,3,2⟩),⟨11,8,(-3)⟩⟩,⟨plan3485,[⟨2,2,3⟩,⟨10,0,4⟩],(some ⟨10,0,4⟩),⟨13,6,(-7)⟩⟩]

def t6_828jobs1 : List Job := [⟨plan3485,[⟨2,2,3⟩,⟨10,1,3⟩],(some ⟨10,1,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3485,[⟨2,2,3⟩,⟨10,1,4⟩],(some ⟨10,1,4⟩),⟨12,6,(-6)⟩⟩,⟨plan3485,[⟨2,2,3⟩,⟨10,2,2⟩],(some ⟨10,2,2⟩),⟨11,8,(-3)⟩⟩,⟨plan3485,[⟨2,2,3⟩,⟨10,2,3⟩],(some ⟨10,2,3⟩),⟨11,7,(-4)⟩⟩]

def t6_828jobs2 : List Job := [⟨plan3485,[⟨2,2,3⟩,⟨10,3,1⟩],(some ⟨10,3,1⟩),⟨10,9,(-1)⟩⟩,⟨plan3485,[⟨2,2,3⟩,⟨10,3,2⟩],(some ⟨10,3,2⟩),⟨10,8,(-2)⟩⟩]

def t6_828jobs : List Job := t6_828jobs0++t6_828jobs1++t6_828jobs2



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


