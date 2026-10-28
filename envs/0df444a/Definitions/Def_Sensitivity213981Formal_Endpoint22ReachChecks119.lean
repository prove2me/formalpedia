-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks119
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks119
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:30:12.722204+00:00
-- url     : https://prove2.me/theorems/c6bc8fd1-931d-46c1-8c73-4d077c8173d4
-- title:
--   Endpoint22 Reach Checks119 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks119 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_978root`, `ThreeBoundEndpoint22Reachable.t6_978jobs0`, `ThreeBoundEndpoint22Reachable.t6_978jobs1`, `ThreeBoundEndpoint22Reachable.t6_978jobs`, `ThreeBoundEndpoint22Reachable.t6_979root`, `ThreeBoundEndpoint22Reachable.t6_979jobs0`, `ThreeBoundEndpoint22Reachable.t6_979jobs`, `ThreeBoundEndpoint22Reachable.t6_980root`, `ThreeBoundEndpoint22Reachable.t6_980jobs0`, `ThreeBoundEndpoint22Reachable.t6_980jobs`, `ThreeBoundEndpoint22Reachable.t6_981root`, `ThreeBoundEndpoint22Reachable.t6_981jobs0`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks119.lean, lines 1–153.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans073
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

def t6_973root : Job := ⟨plan7013,[],none,⟨15,6,0⟩⟩
def t6_973jobs0 : List Job := [⟨plan3363,[⟨4,0,3⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨15,3,(-7)⟩⟩,⟨plan3363,[⟨4,0,3⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3363,[⟨4,0,3⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨14,3,(-7)⟩⟩,⟨plan3363,[⟨4,0,3⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨13,3,(-5)⟩⟩,⟨plan3363,[⟨4,0,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨13,3,(-6)⟩⟩,⟨plan3363,[⟨4,0,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨12,3,(-4)⟩⟩,⟨plan3363,[⟨4,0,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨12,3,(-5)⟩⟩,⟨plan3363,[⟨4,1,2⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨14,4,(-5)⟩⟩,⟨plan3363,[⟨4,1,2⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨13,4,(-4)⟩⟩,⟨plan3363,[⟨4,1,2⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨13,4,(-5)⟩⟩]

def t6_973jobs1 : List Job := [⟨plan3363,[⟨4,1,2⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨12,4,(-3)⟩⟩,⟨plan3363,[⟨4,1,2⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,4,(-4)⟩⟩,⟨plan3363,[⟨4,1,2⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨11,4,(-2)⟩⟩,⟨plan3363,[⟨4,1,2⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,4,(-3)⟩⟩,⟨plan3363,[⟨4,1,3⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨14,3,(-6)⟩⟩,⟨plan3363,[⟨4,1,3⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨13,3,(-5)⟩⟩]

def t6_973jobs2 : List Job := [⟨plan3363,[⟨4,1,3⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨13,3,(-6)⟩⟩,⟨plan3363,[⟨4,1,3⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨12,3,(-4)⟩⟩,⟨plan3363,[⟨4,1,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,3,(-5)⟩⟩,⟨plan3363,[⟨4,1,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨11,3,(-3)⟩⟩,⟨plan3363,[⟨4,1,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,3,(-4)⟩⟩]

def t6_973jobs : List Job := t6_973jobs0++t6_973jobs1++t6_973jobs2




def t6_974root : Job := ⟨plan7014,[],none,⟨15,6,0⟩⟩
def t6_974jobs0 : List Job := [⟨plan3364,[⟨4,0,3⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨15,3,(-7)⟩⟩,⟨plan3364,[⟨4,0,3⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3364,[⟨4,0,3⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨14,3,(-7)⟩⟩,⟨plan3364,[⟨4,0,3⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨13,3,(-5)⟩⟩,⟨plan3364,[⟨4,0,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨13,3,(-6)⟩⟩,⟨plan3364,[⟨4,0,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨12,3,(-4)⟩⟩,⟨plan3364,[⟨4,0,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨12,3,(-5)⟩⟩,⟨plan3364,[⟨4,1,2⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨14,4,(-5)⟩⟩,⟨plan3364,[⟨4,1,2⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨13,4,(-4)⟩⟩,⟨plan3364,[⟨4,1,2⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨13,4,(-5)⟩⟩,⟨plan3364,[⟨4,1,2⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨12,4,(-3)⟩⟩]

def t6_974jobs1 : List Job := [⟨plan3364,[⟨4,1,2⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,4,(-4)⟩⟩,⟨plan3364,[⟨4,1,2⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨11,4,(-2)⟩⟩,⟨plan3364,[⟨4,1,2⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,4,(-3)⟩⟩,⟨plan3364,[⟨4,1,3⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨14,3,(-6)⟩⟩,⟨plan3364,[⟨4,1,3⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3364,[⟨4,1,3⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨13,3,(-6)⟩⟩]

def t6_974jobs2 : List Job := [⟨plan3364,[⟨4,1,3⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨12,3,(-4)⟩⟩,⟨plan3364,[⟨4,1,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,3,(-5)⟩⟩,⟨plan3364,[⟨4,1,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨11,3,(-3)⟩⟩,⟨plan3364,[⟨4,1,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,3,(-4)⟩⟩]

def t6_974jobs : List Job := t6_974jobs0++t6_974jobs1++t6_974jobs2




def t6_975root : Job := ⟨plan7015,[],none,⟨15,6,0⟩⟩
def t6_975jobs0 : List Job := [⟨plan7015,[],none,⟨15,6,0⟩⟩]

def t6_975jobs : List Job := t6_975jobs0




def t6_976root : Job := ⟨plan7016,[],none,⟨15,6,0⟩⟩
def t6_976jobs0 : List Job := [⟨plan5628,[⟨4,0,3⟩],(some ⟨4,0,3⟩),⟨15,3,(-3)⟩⟩]

def t6_976jobs1 : List Job := [⟨plan5628,[⟨4,1,2⟩],(some ⟨4,1,2⟩),⟨14,4,(-1)⟩⟩]

def t6_976jobs2 : List Job := [⟨plan5628,[⟨4,1,3⟩],(some ⟨4,1,3⟩),⟨14,3,(-2)⟩⟩]

def t6_976jobs : List Job := t6_976jobs0++t6_976jobs1++t6_976jobs2




def t6_977root : Job := ⟨plan7017,[],none,⟨15,6,0⟩⟩
def t6_977jobs0 : List Job := [⟨plan3367,[⟨4,0,3⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨15,3,(-7)⟩⟩,⟨plan3367,[⟨4,0,3⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3367,[⟨4,0,3⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨14,3,(-7)⟩⟩,⟨plan3367,[⟨4,0,3⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨13,3,(-5)⟩⟩,⟨plan3367,[⟨4,0,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨13,3,(-6)⟩⟩,⟨plan3367,[⟨4,0,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨12,3,(-4)⟩⟩,⟨plan3367,[⟨4,0,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨12,3,(-5)⟩⟩,⟨plan3367,[⟨4,1,2⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨14,4,(-5)⟩⟩,⟨plan3367,[⟨4,1,2⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨13,4,(-4)⟩⟩,⟨plan3367,[⟨4,1,2⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨13,4,(-5)⟩⟩]

def t6_977jobs1 : List Job := [⟨plan3367,[⟨4,1,2⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨12,4,(-3)⟩⟩,⟨plan3367,[⟨4,1,2⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,4,(-4)⟩⟩,⟨plan3367,[⟨4,1,2⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨11,4,(-2)⟩⟩,⟨plan3367,[⟨4,1,2⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,4,(-3)⟩⟩,⟨plan3367,[⟨4,1,3⟩,⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨14,3,(-6)⟩⟩,⟨plan3367,[⟨4,1,3⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨13,3,(-5)⟩⟩]

def t6_977jobs2 : List Job := [⟨plan3367,[⟨4,1,3⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨13,3,(-6)⟩⟩,⟨plan3367,[⟨4,1,3⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨12,3,(-4)⟩⟩,⟨plan3367,[⟨4,1,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,3,(-5)⟩⟩,⟨plan3367,[⟨4,1,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨11,3,(-3)⟩⟩,⟨plan3367,[⟨4,1,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,3,(-4)⟩⟩]

def t6_977jobs : List Job := t6_977jobs0++t6_977jobs1++t6_977jobs2




def t6_978root : Job := ⟨plan7018,[],none,⟨15,6,0⟩⟩
def t6_978jobs0 : List Job := [⟨plan5630,[⟨4,0,3⟩],(some ⟨4,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5630,[⟨4,1,2⟩],(some ⟨4,1,2⟩),⟨14,4,(-1)⟩⟩]

def t6_978jobs1 : List Job := [⟨plan5630,[⟨4,1,3⟩],(some ⟨4,1,3⟩),⟨14,3,(-2)⟩⟩]

def t6_978jobs : List Job := t6_978jobs0++t6_978jobs1




def t6_979root : Job := ⟨plan7019,[],none,⟨15,6,0⟩⟩
def t6_979jobs0 : List Job := [⟨plan7019,[],none,⟨15,6,0⟩⟩]

def t6_979jobs : List Job := t6_979jobs0




def t6_980root : Job := ⟨plan7464,[],none,⟨15,10,0⟩⟩
def t6_980jobs0 : List Job := [⟨plan7464,[],none,⟨15,10,0⟩⟩]

def t6_980jobs : List Job := t6_980jobs0




def t6_981root : Job := ⟨plan7465,[],none,⟨15,10,0⟩⟩
def t6_981jobs0 : List Job := [⟨plan7465,[],none,⟨15,10,0⟩⟩]

def t6_981jobs : List Job := t6_981jobs0




def t6_982root : Job := ⟨plan7466,[],none,⟨15,10,0⟩⟩
def t6_982jobs0 : List Job := [⟨plan7466,[],none,⟨15,10,0⟩⟩]

def t6_982jobs : List Job := t6_982jobs0




def t6_983root : Job := ⟨plan7467,[],none,⟨15,10,0⟩⟩
def t6_983jobs0 : List Job := [⟨plan5773,[⟨4,0,4⟩],(some ⟨4,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5773,[⟨4,1,3⟩],(some ⟨4,1,3⟩),⟨14,7,(-2)⟩⟩]

def t6_983jobs1 : List Job := [⟨plan5773,[⟨4,1,4⟩],(some ⟨4,1,4⟩),⟨14,6,(-3)⟩⟩]

def t6_983jobs : List Job := t6_983jobs0++t6_983jobs1



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


