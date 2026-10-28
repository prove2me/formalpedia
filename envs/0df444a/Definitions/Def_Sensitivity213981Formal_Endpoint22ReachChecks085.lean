-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks085
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks085
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:27:58.072458+00:00
-- url     : https://prove2.me/theorems/d4fc2a7e-df3c-4ca5-a80a-23efe42b9b47
-- title:
--   Endpoint22 Reach Checks085 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks085 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_687jobs0`, `ThreeBoundEndpoint22Reachable.t6_687jobs`, `ThreeBoundEndpoint22Reachable.t6_688root`, `ThreeBoundEndpoint22Reachable.t6_688jobs0`, `ThreeBoundEndpoint22Reachable.t6_688jobs1`, `ThreeBoundEndpoint22Reachable.t6_688jobs`, `ThreeBoundEndpoint22Reachable.t6_689root`, `ThreeBoundEndpoint22Reachable.t6_689jobs0`, `ThreeBoundEndpoint22Reachable.t6_689jobs`, `ThreeBoundEndpoint22Reachable.t6_690root`, `ThreeBoundEndpoint22Reachable.t6_690jobs0`, `ThreeBoundEndpoint22Reachable.t6_690jobs`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks085.lean, lines 1–133.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans066
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

def t6_683root : Job := ⟨plan6936,[],none,⟨15,6,0⟩⟩
def t6_683jobs0 : List Job := [⟨plan3367,[⟨2,0,4⟩,⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨15,3,(-7)⟩⟩,⟨plan3367,[⟨2,0,4⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨14,4,(-5)⟩⟩,⟨plan3367,[⟨2,0,4⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3367,[⟨2,0,4⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨13,5,(-3)⟩⟩,⟨plan3367,[⟨2,0,4⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨13,4,(-4)⟩⟩,⟨plan3367,[⟨2,0,4⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3367,[⟨2,1,3⟩,⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3367,[⟨2,1,3⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨13,4,(-4)⟩⟩,⟨plan3367,[⟨2,1,3⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3367,[⟨2,1,3⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨12,5,(-2)⟩⟩]

def t6_683jobs1 : List Job := [⟨plan3367,[⟨2,1,3⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨12,4,(-3)⟩⟩,⟨plan3367,[⟨2,1,3⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨12,3,(-4)⟩⟩,⟨plan3367,[⟨2,1,4⟩,⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨14,3,(-7)⟩⟩,⟨plan3367,[⟨2,1,4⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨13,4,(-5)⟩⟩,⟨plan3367,[⟨2,1,4⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨13,3,(-6)⟩⟩]

def t6_683jobs2 : List Job := [⟨plan3367,[⟨2,1,4⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨12,5,(-3)⟩⟩,⟨plan3367,[⟨2,1,4⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨12,4,(-4)⟩⟩,⟨plan3367,[⟨2,1,4⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨12,3,(-5)⟩⟩,⟨plan3367,[⟨2,2,2⟩,⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨13,3,(-5)⟩⟩]

def t6_683jobs3 : List Job := [⟨plan3367,[⟨2,2,2⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨12,4,(-3)⟩⟩,⟨plan3367,[⟨2,2,2⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨12,3,(-4)⟩⟩]

def t6_683jobs4 : List Job := [⟨plan3367,[⟨2,2,2⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨11,5,(-1)⟩⟩]

def t6_683jobs5 : List Job := [⟨plan3367,[⟨2,2,2⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨11,4,(-2)⟩⟩]

def t6_683jobs6 : List Job := [⟨plan3367,[⟨2,2,2⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨11,3,(-3)⟩⟩,⟨plan3367,[⟨2,2,3⟩,⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨13,3,(-6)⟩⟩]

def t6_683jobs7 : List Job := [⟨plan3367,[⟨2,2,3⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨12,4,(-4)⟩⟩,⟨plan3367,[⟨2,2,3⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨12,3,(-5)⟩⟩]

def t6_683jobs8 : List Job := [⟨plan3367,[⟨2,2,3⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨11,5,(-2)⟩⟩]

def t6_683jobs9 : List Job := [⟨plan3367,[⟨2,2,3⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨11,4,(-3)⟩⟩]

def t6_683jobs10 : List Job := [⟨plan3367,[⟨2,2,3⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨11,3,(-4)⟩⟩]

def t6_683jobs : List Job := t6_683jobs0++t6_683jobs1++t6_683jobs2++t6_683jobs3++t6_683jobs4++t6_683jobs5++t6_683jobs6++t6_683jobs7++t6_683jobs8++t6_683jobs9++t6_683jobs10




def t6_684root : Job := ⟨plan6937,[],none,⟨15,6,0⟩⟩
def t6_684jobs0 : List Job := [⟨plan3368,[⟨2,0,4⟩,⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨15,3,(-7)⟩⟩,⟨plan3368,[⟨2,0,4⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨14,4,(-5)⟩⟩,⟨plan3368,[⟨2,0,4⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3368,[⟨2,0,4⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨13,5,(-3)⟩⟩,⟨plan3368,[⟨2,0,4⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨13,4,(-4)⟩⟩,⟨plan3368,[⟨2,0,4⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3368,[⟨2,1,3⟩,⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3368,[⟨2,1,3⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨13,4,(-4)⟩⟩,⟨plan3368,[⟨2,1,3⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3368,[⟨2,1,3⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨12,5,(-2)⟩⟩,⟨plan3368,[⟨2,1,3⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨12,4,(-3)⟩⟩,⟨plan3368,[⟨2,1,3⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨12,3,(-4)⟩⟩,⟨plan3368,[⟨2,1,4⟩,⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨14,3,(-7)⟩⟩,⟨plan3368,[⟨2,1,4⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨13,4,(-5)⟩⟩,⟨plan3368,[⟨2,1,4⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨13,3,(-6)⟩⟩,⟨plan3368,[⟨2,1,4⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨12,5,(-3)⟩⟩]

def t6_684jobs1 : List Job := [⟨plan3368,[⟨2,1,4⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨12,4,(-4)⟩⟩,⟨plan3368,[⟨2,1,4⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨12,3,(-5)⟩⟩,⟨plan3368,[⟨2,2,2⟩,⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3368,[⟨2,2,2⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨12,4,(-3)⟩⟩,⟨plan3368,[⟨2,2,2⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨12,3,(-4)⟩⟩]

def t6_684jobs2 : List Job := [⟨plan3368,[⟨2,2,2⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨11,5,(-1)⟩⟩,⟨plan3368,[⟨2,2,2⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨11,4,(-2)⟩⟩]

def t6_684jobs3 : List Job := [⟨plan3368,[⟨2,2,2⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨11,3,(-3)⟩⟩,⟨plan3368,[⟨2,2,3⟩,⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨13,3,(-6)⟩⟩,⟨plan3368,[⟨2,2,3⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨12,4,(-4)⟩⟩,⟨plan3368,[⟨2,2,3⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨12,3,(-5)⟩⟩]

def t6_684jobs4 : List Job := [⟨plan3368,[⟨2,2,3⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨11,5,(-2)⟩⟩,⟨plan3368,[⟨2,2,3⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨11,4,(-3)⟩⟩]

def t6_684jobs5 : List Job := [⟨plan3368,[⟨2,2,3⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨11,3,(-4)⟩⟩]

def t6_684jobs : List Job := t6_684jobs0++t6_684jobs1++t6_684jobs2++t6_684jobs3++t6_684jobs4++t6_684jobs5




def t6_685root : Job := ⟨plan6938,[],none,⟨15,6,0⟩⟩
def t6_685jobs0 : List Job := [⟨plan6938,[],none,⟨15,6,0⟩⟩]

def t6_685jobs : List Job := t6_685jobs0




def t6_686root : Job := ⟨plan6395,[],none,⟨15,1,0⟩⟩
def t6_686jobs0 : List Job := [⟨plan6395,[],none,⟨15,1,0⟩⟩]

def t6_686jobs : List Job := t6_686jobs0




def t6_687root : Job := ⟨plan6593,[],none,⟨15,3,0⟩⟩
def t6_687jobs0 : List Job := [⟨plan6593,[],none,⟨15,3,0⟩⟩]

def t6_687jobs : List Job := t6_687jobs0




def t6_688root : Job := ⟨plan6594,[],none,⟨15,3,0⟩⟩
def t6_688jobs0 : List Job := [⟨plan5512,[⟨2,0,3⟩],(some ⟨2,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5512,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨14,3,(-2)⟩⟩,⟨plan5512,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨14,3,(-3)⟩⟩,⟨plan5512,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨13,3,(-1)⟩⟩,⟨plan5512,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨13,3,(-2)⟩⟩]

def t6_688jobs1 : List Job := [⟨plan5512,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨13,3,(-3)⟩⟩]

def t6_688jobs : List Job := t6_688jobs0++t6_688jobs1




def t6_689root : Job := ⟨plan6595,[],none,⟨15,3,0⟩⟩
def t6_689jobs0 : List Job := [⟨plan6595,[],none,⟨15,3,0⟩⟩]

def t6_689jobs : List Job := t6_689jobs0




def t6_690root : Job := ⟨plan6939,[],none,⟨15,6,0⟩⟩
def t6_690jobs0 : List Job := [⟨plan6939,[],none,⟨15,6,0⟩⟩]

def t6_690jobs : List Job := t6_690jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


