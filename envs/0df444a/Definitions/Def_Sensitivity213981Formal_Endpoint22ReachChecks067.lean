-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks067
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks067
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:25:23.207881+00:00
-- url     : https://prove2.me/theorems/480fa486-d506-408b-a539-2b1b98070139
-- title:
--   Endpoint22 Reach Checks067 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks067 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_620root`, `ThreeBoundEndpoint22Reachable.t6_620jobs0`, `ThreeBoundEndpoint22Reachable.t6_620jobs`, `ThreeBoundEndpoint22Reachable.t6_610jobs3`, `ThreeBoundEndpoint22Reachable.t6_621root`, `ThreeBoundEndpoint22Reachable.t6_621jobs0`, `ThreeBoundEndpoint22Reachable.t6_621jobs`, `ThreeBoundEndpoint22Reachable.t6_622root`, `ThreeBoundEndpoint22Reachable.t6_622jobs0`, `ThreeBoundEndpoint22Reachable.t6_622jobs`, `ThreeBoundEndpoint22Reachable.t6_623root`, `ThreeBoundEndpoint22Reachable.t6_623jobs0`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks067.lean, lines 1–232.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans068
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans071
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

def t6_610root : Job := ⟨plan6573,[],none,⟨15,3,0⟩⟩
def t6_610jobs0 : List Job := [⟨plan5476,[⟨2,0,3⟩],(some ⟨2,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5476,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨14,3,(-2)⟩⟩]

def t6_610jobs1 : List Job := [⟨plan5476,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨14,3,(-3)⟩⟩]

def t6_610jobs2 : List Job := [⟨plan5476,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨13,3,(-1)⟩⟩]

def t6_610jobs3 : List Job := [⟨plan5476,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨13,3,(-2)⟩⟩,⟨plan5476,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨13,3,(-3)⟩⟩]

def t6_610jobs : List Job := t6_610jobs0++t6_610jobs1++t6_610jobs2++t6_610jobs3




def t6_611root : Job := ⟨plan6574,[],none,⟨15,3,0⟩⟩
def t6_611jobs0 : List Job := [⟨plan5477,[⟨2,0,3⟩],(some ⟨2,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5477,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨14,3,(-2)⟩⟩,⟨plan5477,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨14,3,(-3)⟩⟩]

def t6_611jobs1 : List Job := [⟨plan5477,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨13,3,(-1)⟩⟩]

def t6_611jobs2 : List Job := [⟨plan5477,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨13,3,(-2)⟩⟩,⟨plan5477,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨13,3,(-3)⟩⟩]

def t6_611jobs : List Job := t6_611jobs0++t6_611jobs1++t6_611jobs2




def t6_612root : Job := ⟨plan6575,[],none,⟨15,3,0⟩⟩
def t6_612jobs0 : List Job := [⟨plan6575,[],none,⟨15,3,0⟩⟩]

def t6_612jobs : List Job := t6_612jobs0




def t6_613root : Job := ⟨plan6897,[],none,⟨15,6,0⟩⟩
def t6_613jobs0 : List Job := [⟨plan6897,[],none,⟨15,6,0⟩⟩]

def t6_613jobs : List Job := t6_613jobs0




def t6_614root : Job := ⟨plan6898,[],none,⟨15,6,0⟩⟩
def t6_614jobs0 : List Job := [⟨plan6898,[],none,⟨15,6,0⟩⟩]

def t6_614jobs : List Job := t6_614jobs0




def t6_615root : Job := ⟨plan6899,[],none,⟨15,6,0⟩⟩
def t6_615jobs0 : List Job := [⟨plan6899,[],none,⟨15,6,0⟩⟩]

def t6_615jobs : List Job := t6_615jobs0




def t6_616root : Job := ⟨plan6900,[],none,⟨15,6,0⟩⟩
def t6_616jobs0 : List Job := [⟨plan5608,[⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5608,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨14,6,(-3)⟩⟩,⟨plan5608,[⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨14,6,(-4)⟩⟩]

def t6_616jobs1 : List Job := [⟨plan5608,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨13,6,(-2)⟩⟩,⟨plan5608,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨13,6,(-3)⟩⟩]

def t6_616jobs : List Job := t6_616jobs0++t6_616jobs1




def t6_617root : Job := ⟨plan6901,[],none,⟨15,6,0⟩⟩
def t6_617jobs0 : List Job := [⟨plan5609,[⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5609,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨14,6,(-3)⟩⟩,⟨plan5609,[⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨14,6,(-4)⟩⟩]

def t6_617jobs1 : List Job := [⟨plan5609,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨13,6,(-2)⟩⟩,⟨plan5609,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨13,6,(-3)⟩⟩]

def t6_617jobs : List Job := t6_617jobs0++t6_617jobs1




def t6_618root : Job := ⟨plan6902,[],none,⟨15,6,0⟩⟩
def t6_618jobs0 : List Job := [⟨plan6902,[],none,⟨15,6,0⟩⟩]

def t6_618jobs : List Job := t6_618jobs0




def t6_619root : Job := ⟨plan6903,[],none,⟨15,6,0⟩⟩
def t6_619jobs0 : List Job := [⟨plan5611,[⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5611,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨14,6,(-3)⟩⟩,⟨plan5611,[⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨14,6,(-4)⟩⟩]

def t6_619jobs1 : List Job := [⟨plan5611,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨13,6,(-2)⟩⟩,⟨plan5611,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨13,6,(-3)⟩⟩]

def t6_619jobs : List Job := t6_619jobs0++t6_619jobs1




def t6_620root : Job := ⟨plan6576,[],none,⟨15,3,0⟩⟩
def t6_620jobs0 : List Job := [⟨plan6576,[],none,⟨15,3,0⟩⟩]

def t6_620jobs : List Job := t6_620jobs0




def t6_621root : Job := ⟨plan6904,[],none,⟨15,6,0⟩⟩
def t6_621jobs0 : List Job := [⟨plan6904,[],none,⟨15,6,0⟩⟩]

def t6_621jobs : List Job := t6_621jobs0




def t6_622root : Job := ⟨plan6905,[],none,⟨15,6,0⟩⟩
def t6_622jobs0 : List Job := [⟨plan6905,[],none,⟨15,6,0⟩⟩]

def t6_622jobs : List Job := t6_622jobs0




def t6_623root : Job := ⟨plan6906,[],none,⟨15,6,0⟩⟩
def t6_623jobs0 : List Job := [⟨plan6906,[],none,⟨15,6,0⟩⟩]

def t6_623jobs : List Job := t6_623jobs0




def t6_624root : Job := ⟨plan6907,[],none,⟨15,6,0⟩⟩
def t6_624jobs0 : List Job := [⟨plan5615,[⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5615,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨14,6,(-3)⟩⟩,⟨plan5615,[⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨14,6,(-4)⟩⟩]

def t6_624jobs1 : List Job := [⟨plan5615,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨13,6,(-2)⟩⟩,⟨plan5615,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨13,6,(-3)⟩⟩]

def t6_624jobs : List Job := t6_624jobs0++t6_624jobs1




def t6_625root : Job := ⟨plan6908,[],none,⟨15,6,0⟩⟩
def t6_625jobs0 : List Job := [⟨plan6908,[],none,⟨15,6,0⟩⟩]

def t6_625jobs : List Job := t6_625jobs0




def t6_626root : Job := ⟨plan6909,[],none,⟨15,6,0⟩⟩
def t6_626jobs0 : List Job := [⟨plan6909,[],none,⟨15,6,0⟩⟩]

def t6_626jobs : List Job := t6_626jobs0




def t6_627root : Job := ⟨plan6910,[],none,⟨15,6,0⟩⟩
def t6_627jobs0 : List Job := [⟨plan5618,[⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5618,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨14,6,(-3)⟩⟩]

def t6_627jobs1 : List Job := [⟨plan5618,[⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨14,6,(-4)⟩⟩]

def t6_627jobs2 : List Job := [⟨plan5618,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨13,6,(-2)⟩⟩,⟨plan5618,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨13,6,(-3)⟩⟩]

def t6_627jobs : List Job := t6_627jobs0++t6_627jobs1++t6_627jobs2



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


