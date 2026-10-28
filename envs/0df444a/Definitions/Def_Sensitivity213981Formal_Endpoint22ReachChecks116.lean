-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks116
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks116
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:29:51.440559+00:00
-- url     : https://prove2.me/theorems/c228dc21-bfa1-405f-b5b4-0bf568a300d6
-- title:
--   Endpoint22 Reach Checks116 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks116 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_910root`, `ThreeBoundEndpoint22Reachable.t6_910jobs0`, `ThreeBoundEndpoint22Reachable.t6_910jobs1`, `ThreeBoundEndpoint22Reachable.t6_910jobs`, `ThreeBoundEndpoint22Reachable.t6_911root`, `ThreeBoundEndpoint22Reachable.t6_911jobs0`, `ThreeBoundEndpoint22Reachable.t6_911jobs`, `ThreeBoundEndpoint22Reachable.t6_912root`, `ThreeBoundEndpoint22Reachable.t6_912jobs0`, `ThreeBoundEndpoint22Reachable.t6_912jobs`, `ThreeBoundEndpoint22Reachable.t6_913root`, `ThreeBoundEndpoint22Reachable.t6_913jobs0`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks116.lean, lines 1–264.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans065
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans066
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans068
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans069
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

def t6_898root : Job := ⟨plan6990,[],none,⟨15,6,0⟩⟩
def t6_898jobs0 : List Job := [⟨plan6990,[],none,⟨15,6,0⟩⟩]

def t6_898jobs : List Job := t6_898jobs0




def t6_899root : Job := ⟨plan6991,[],none,⟨15,6,0⟩⟩
def t6_899jobs0 : List Job := [⟨plan6991,[],none,⟨15,6,0⟩⟩]

def t6_899jobs : List Job := t6_899jobs0




def t6_900root : Job := ⟨plan6992,[],none,⟨15,6,0⟩⟩
def t6_900jobs0 : List Job := [⟨plan6992,[],none,⟨15,6,0⟩⟩]

def t6_900jobs : List Job := t6_900jobs0




def t6_901root : Job := ⟨plan6993,[],none,⟨15,6,0⟩⟩
def t6_901jobs0 : List Job := [⟨plan6993,[],none,⟨15,6,0⟩⟩]

def t6_901jobs : List Job := t6_901jobs0




def t6_902root : Job := ⟨plan6314,[],none,⟨15,0,0⟩⟩
def t6_902jobs0 : List Job := [⟨plan6314,[],none,⟨15,0,0⟩⟩]

def t6_902jobs : List Job := t6_902jobs0




def t6_903root : Job := ⟨plan6408,[],none,⟨15,1,0⟩⟩
def t6_903jobs0 : List Job := [⟨plan6408,[],none,⟨15,1,0⟩⟩]

def t6_903jobs : List Job := t6_903jobs0




def t6_904root : Job := ⟨plan6409,[],none,⟨15,1,0⟩⟩
def t6_904jobs0 : List Job := [⟨plan6409,[],none,⟨15,1,0⟩⟩]

def t6_904jobs : List Job := t6_904jobs0




def t6_905root : Job := ⟨plan6410,[],none,⟨15,1,0⟩⟩
def t6_905jobs0 : List Job := [⟨plan6410,[],none,⟨15,1,0⟩⟩]

def t6_905jobs : List Job := t6_905jobs0




def t6_906root : Job := ⟨plan6622,[],none,⟨15,3,0⟩⟩
def t6_906jobs0 : List Job := [⟨plan6622,[],none,⟨15,3,0⟩⟩]

def t6_906jobs : List Job := t6_906jobs0




def t6_907root : Job := ⟨plan6623,[],none,⟨15,3,0⟩⟩
def t6_907jobs0 : List Job := [⟨plan5448,[⟨4,0,2⟩],(some ⟨4,0,2⟩),⟨15,1,(-2)⟩⟩,⟨plan5448,[⟨4,1,1⟩],(some ⟨4,1,1⟩),⟨14,2,0⟩⟩]

def t6_907jobs1 : List Job := [⟨plan5448,[⟨4,1,2⟩],(some ⟨4,1,2⟩),⟨14,1,(-1)⟩⟩]

def t6_907jobs : List Job := t6_907jobs0++t6_907jobs1




def t6_908root : Job := ⟨plan6624,[],none,⟨15,3,0⟩⟩
def t6_908jobs0 : List Job := [⟨plan6624,[],none,⟨15,3,0⟩⟩]

def t6_908jobs : List Job := t6_908jobs0




def t6_909root : Job := ⟨plan6625,[],none,⟨15,3,0⟩⟩
def t6_909jobs0 : List Job := [⟨plan5450,[⟨4,0,2⟩],(some ⟨4,0,2⟩),⟨15,1,(-2)⟩⟩]

def t6_909jobs1 : List Job := [⟨plan5450,[⟨4,1,1⟩],(some ⟨4,1,1⟩),⟨14,2,0⟩⟩]

def t6_909jobs2 : List Job := [⟨plan5450,[⟨4,1,2⟩],(some ⟨4,1,2⟩),⟨14,1,(-1)⟩⟩]

def t6_909jobs : List Job := t6_909jobs0++t6_909jobs1++t6_909jobs2




def t6_910root : Job := ⟨plan6626,[],none,⟨15,3,0⟩⟩
def t6_910jobs0 : List Job := [⟨plan5451,[⟨4,0,2⟩],(some ⟨4,0,2⟩),⟨15,1,(-2)⟩⟩,⟨plan5451,[⟨4,1,1⟩],(some ⟨4,1,1⟩),⟨14,2,0⟩⟩]

def t6_910jobs1 : List Job := [⟨plan5451,[⟨4,1,2⟩],(some ⟨4,1,2⟩),⟨14,1,(-1)⟩⟩]

def t6_910jobs : List Job := t6_910jobs0++t6_910jobs1




def t6_911root : Job := ⟨plan6627,[],none,⟨15,3,0⟩⟩
def t6_911jobs0 : List Job := [⟨plan6627,[],none,⟨15,3,0⟩⟩]

def t6_911jobs : List Job := t6_911jobs0




def t6_912root : Job := ⟨plan6994,[],none,⟨15,6,0⟩⟩
def t6_912jobs0 : List Job := [⟨plan6994,[],none,⟨15,6,0⟩⟩]

def t6_912jobs : List Job := t6_912jobs0




def t6_913root : Job := ⟨plan6995,[],none,⟨15,6,0⟩⟩
def t6_913jobs0 : List Job := [⟨plan5563,[⟨4,0,3⟩],(some ⟨4,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5563,[⟨4,1,2⟩],(some ⟨4,1,2⟩),⟨14,4,(-1)⟩⟩]

def t6_913jobs1 : List Job := [⟨plan5563,[⟨4,1,3⟩],(some ⟨4,1,3⟩),⟨14,3,(-2)⟩⟩]

def t6_913jobs : List Job := t6_913jobs0++t6_913jobs1




def t6_914root : Job := ⟨plan6996,[],none,⟨15,6,0⟩⟩
def t6_914jobs0 : List Job := [⟨plan6996,[],none,⟨15,6,0⟩⟩]

def t6_914jobs : List Job := t6_914jobs0




def t6_915root : Job := ⟨plan6997,[],none,⟨15,6,0⟩⟩
def t6_915jobs0 : List Job := [⟨plan3363,[⟨4,0,3⟩,⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨15,3,(-7)⟩⟩,⟨plan3363,[⟨4,0,3⟩,⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3363,[⟨4,0,3⟩,⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨14,3,(-7)⟩⟩,⟨plan3363,[⟨4,0,3⟩,⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨13,3,(-5)⟩⟩,⟨plan3363,[⟨4,0,3⟩,⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨13,3,(-6)⟩⟩,⟨plan3363,[⟨4,1,2⟩,⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨14,4,(-5)⟩⟩,⟨plan3363,[⟨4,1,2⟩,⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨13,4,(-4)⟩⟩,⟨plan3363,[⟨4,1,2⟩,⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨13,4,(-5)⟩⟩,⟨plan3363,[⟨4,1,2⟩,⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨12,4,(-3)⟩⟩]

def t6_915jobs1 : List Job := [⟨plan3363,[⟨4,1,2⟩,⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨12,4,(-4)⟩⟩,⟨plan3363,[⟨4,1,3⟩,⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨14,3,(-6)⟩⟩,⟨plan3363,[⟨4,1,3⟩,⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3363,[⟨4,1,3⟩,⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨13,3,(-6)⟩⟩,⟨plan3363,[⟨4,1,3⟩,⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨12,3,(-4)⟩⟩]

def t6_915jobs2 : List Job := [⟨plan3363,[⟨4,1,3⟩,⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨12,3,(-5)⟩⟩]

def t6_915jobs : List Job := t6_915jobs0++t6_915jobs1++t6_915jobs2




def t6_916root : Job := ⟨plan6998,[],none,⟨15,6,0⟩⟩
def t6_916jobs0 : List Job := [⟨plan5566,[⟨4,0,3⟩],(some ⟨4,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5566,[⟨4,1,2⟩],(some ⟨4,1,2⟩),⟨14,4,(-1)⟩⟩]

def t6_916jobs1 : List Job := [⟨plan5566,[⟨4,1,3⟩],(some ⟨4,1,3⟩),⟨14,3,(-2)⟩⟩]

def t6_916jobs : List Job := t6_916jobs0++t6_916jobs1




def t6_917root : Job := ⟨plan6999,[],none,⟨15,6,0⟩⟩
def t6_917jobs0 : List Job := [⟨plan6999,[],none,⟨15,6,0⟩⟩]

def t6_917jobs : List Job := t6_917jobs0




def t6_918root : Job := ⟨plan7000,[],none,⟨15,6,0⟩⟩
def t6_918jobs0 : List Job := [⟨plan5568,[⟨4,0,3⟩],(some ⟨4,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5568,[⟨4,1,2⟩],(some ⟨4,1,2⟩),⟨14,4,(-1)⟩⟩]

def t6_918jobs1 : List Job := [⟨plan5568,[⟨4,1,3⟩],(some ⟨4,1,3⟩),⟨14,3,(-2)⟩⟩]

def t6_918jobs : List Job := t6_918jobs0++t6_918jobs1



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


