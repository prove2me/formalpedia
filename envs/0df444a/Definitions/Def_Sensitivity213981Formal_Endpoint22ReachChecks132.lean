-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks132
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks132
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:29:40.620052+00:00
-- url     : https://prove2.me/theorems/aae7cf79-87a4-4694-83d3-35a0fc705ebd
-- title:
--   Endpoint22 Reach Checks132 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks132 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_1230root`, `ThreeBoundEndpoint22Reachable.t6_1230jobs0`, `ThreeBoundEndpoint22Reachable.t6_1230jobs1`, `ThreeBoundEndpoint22Reachable.t6_1230jobs2`, `ThreeBoundEndpoint22Reachable.t6_1230jobs`, `ThreeBoundEndpoint22Reachable.t6_1220jobs`, `ThreeBoundEndpoint22Reachable.t6_1231root`, `ThreeBoundEndpoint22Reachable.t6_1231jobs0`, `ThreeBoundEndpoint22Reachable.t6_1231jobs`, `ThreeBoundEndpoint22Reachable.t6_1232root`, `ThreeBoundEndpoint22Reachable.t6_1232jobs0`, `ThreeBoundEndpoint22Reachable.t6_1232jobs`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks132.lean, lines 1–199.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans066
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans069
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

def t6_1220root : Job := ⟨plan7543,[],none,⟨15,10,0⟩⟩
def t6_1220jobs0 : List Job := [⟨plan5783,[⟨5,0,4⟩],(some ⟨5,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5783,[⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨14,7,(-2)⟩⟩,⟨plan5783,[⟨5,1,4⟩],(some ⟨5,1,4⟩),⟨14,6,(-3)⟩⟩]

def t6_1220jobs1 : List Job := [⟨plan5783,[⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨13,8,0⟩⟩,⟨plan5783,[⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨13,7,(-1)⟩⟩]

def t6_1220jobs : List Job := t6_1220jobs0++t6_1220jobs1




def t6_1221root : Job := ⟨plan7544,[],none,⟨15,10,0⟩⟩
def t6_1221jobs0 : List Job := [⟨plan7544,[],none,⟨15,10,0⟩⟩]

def t6_1221jobs : List Job := t6_1221jobs0




def t6_1222root : Job := ⟨plan6419,[],none,⟨15,1,0⟩⟩
def t6_1222jobs0 : List Job := [⟨plan6419,[],none,⟨15,1,0⟩⟩]

def t6_1222jobs : List Job := t6_1222jobs0




def t6_1223root : Job := ⟨plan6650,[],none,⟨15,3,0⟩⟩
def t6_1223jobs0 : List Job := [⟨plan6650,[],none,⟨15,3,0⟩⟩]

def t6_1223jobs : List Job := t6_1223jobs0




def t6_1224root : Job := ⟨plan6651,[],none,⟨15,3,0⟩⟩
def t6_1224jobs0 : List Job := [⟨plan5502,[⟨5,0,2⟩],(some ⟨5,0,2⟩),⟨15,1,(-2)⟩⟩,⟨plan5502,[⟨5,1,1⟩],(some ⟨5,1,1⟩),⟨14,2,0⟩⟩,⟨plan5502,[⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨14,1,(-1)⟩⟩]

def t6_1224jobs1 : List Job := [⟨plan5502,[⟨5,2,0⟩],(some ⟨5,2,0⟩),⟨13,3,2⟩⟩,⟨plan5502,[⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨13,2,1⟩⟩,⟨plan5502,[⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨13,1,0⟩⟩]

def t6_1224jobs : List Job := t6_1224jobs0++t6_1224jobs1




def t6_1225root : Job := ⟨plan6652,[],none,⟨15,3,0⟩⟩
def t6_1225jobs0 : List Job := [⟨plan6652,[],none,⟨15,3,0⟩⟩]

def t6_1225jobs : List Job := t6_1225jobs0




def t6_1226root : Job := ⟨plan7053,[],none,⟨15,6,0⟩⟩
def t6_1226jobs0 : List Job := [⟨plan7053,[],none,⟨15,6,0⟩⟩]

def t6_1226jobs : List Job := t6_1226jobs0




def t6_1227root : Job := ⟨plan7054,[],none,⟨15,6,0⟩⟩
def t6_1227jobs0 : List Job := [⟨plan5663,[⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5663,[⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨14,4,(-1)⟩⟩,⟨plan5663,[⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨14,3,(-2)⟩⟩]

def t6_1227jobs1 : List Job := [⟨plan5663,[⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨13,5,1⟩⟩]

def t6_1227jobs2 : List Job := [⟨plan5663,[⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨13,4,0⟩⟩,⟨plan5663,[⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨13,3,(-1)⟩⟩]

def t6_1227jobs : List Job := t6_1227jobs0++t6_1227jobs1++t6_1227jobs2




def t6_1228root : Job := ⟨plan7055,[],none,⟨15,6,0⟩⟩
def t6_1228jobs0 : List Job := [⟨plan7055,[],none,⟨15,6,0⟩⟩]

def t6_1228jobs : List Job := t6_1228jobs0




def t6_1229root : Job := ⟨plan7056,[],none,⟨15,6,0⟩⟩
def t6_1229jobs0 : List Job := [⟨plan5665,[⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5665,[⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨14,4,(-1)⟩⟩]

def t6_1229jobs1 : List Job := [⟨plan5665,[⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨14,3,(-2)⟩⟩]

def t6_1229jobs2 : List Job := [⟨plan5665,[⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨13,5,1⟩⟩]

def t6_1229jobs3 : List Job := [⟨plan5665,[⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨13,4,0⟩⟩,⟨plan5665,[⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨13,3,(-1)⟩⟩]

def t6_1229jobs : List Job := t6_1229jobs0++t6_1229jobs1++t6_1229jobs2++t6_1229jobs3




def t6_1230root : Job := ⟨plan7057,[],none,⟨15,6,0⟩⟩
def t6_1230jobs0 : List Job := [⟨plan5666,[⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5666,[⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨14,4,(-1)⟩⟩,⟨plan5666,[⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨14,3,(-2)⟩⟩]

def t6_1230jobs1 : List Job := [⟨plan5666,[⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨13,5,1⟩⟩]

def t6_1230jobs2 : List Job := [⟨plan5666,[⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨13,4,0⟩⟩,⟨plan5666,[⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨13,3,(-1)⟩⟩]

def t6_1230jobs : List Job := t6_1230jobs0++t6_1230jobs1++t6_1230jobs2




def t6_1231root : Job := ⟨plan7058,[],none,⟨15,6,0⟩⟩
def t6_1231jobs0 : List Job := [⟨plan7058,[],none,⟨15,6,0⟩⟩]

def t6_1231jobs : List Job := t6_1231jobs0




def t6_1232root : Job := ⟨plan7545,[],none,⟨15,10,0⟩⟩
def t6_1232jobs0 : List Job := [⟨plan7545,[],none,⟨15,10,0⟩⟩]

def t6_1232jobs : List Job := t6_1232jobs0




def t6_1233root : Job := ⟨plan7546,[],none,⟨15,10,0⟩⟩
def t6_1233jobs0 : List Job := [⟨plan5815,[⟨5,0,4⟩],(some ⟨5,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5815,[⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨14,7,(-2)⟩⟩,⟨plan5815,[⟨5,1,4⟩],(some ⟨5,1,4⟩),⟨14,6,(-3)⟩⟩,⟨plan5815,[⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨13,8,0⟩⟩]

def t6_1233jobs1 : List Job := [⟨plan5815,[⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨13,7,(-1)⟩⟩]

def t6_1233jobs : List Job := t6_1233jobs0++t6_1233jobs1




def t6_1234root : Job := ⟨plan7547,[],none,⟨15,10,0⟩⟩
def t6_1234jobs0 : List Job := [⟨plan7547,[],none,⟨15,10,0⟩⟩]

def t6_1234jobs : List Job := t6_1234jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


