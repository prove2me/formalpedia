-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks114
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks114
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:27:16.040668+00:00
-- url     : https://prove2.me/theorems/723cba2e-3a43-4c9a-acb7-26e1419313f7
-- title:
--   Endpoint22 Reach Checks114 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks114 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_880jobs1`, `ThreeBoundEndpoint22Reachable.t6_880jobs2`, `ThreeBoundEndpoint22Reachable.t6_880jobs3`, `ThreeBoundEndpoint22Reachable.t6_880jobs4`, `ThreeBoundEndpoint22Reachable.t6_880jobs5`, `ThreeBoundEndpoint22Reachable.t6_880jobs6`, `ThreeBoundEndpoint22Reachable.t6_880jobs7`, `ThreeBoundEndpoint22Reachable.t6_880jobs8`, `ThreeBoundEndpoint22Reachable.t6_880jobs`, `ThreeBoundEndpoint22Reachable.t6_880root`, `ThreeBoundEndpoint22Reachable.t6_881root`, `ThreeBoundEndpoint22Reachable.t6_881jobs0`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks114.lean, lines 1–81.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
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

def t6_880root : Job := ⟨plan7425,[],none,⟨15,10,0⟩⟩
def t6_880jobs0 : List Job := [⟨plan3508,[⟨3,0,5⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3508,[⟨3,0,5⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3508,[⟨3,0,5⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3508,[⟨3,0,5⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨13,8,(-5)⟩⟩,⟨plan3508,[⟨3,0,5⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3508,[⟨3,0,5⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨12,9,(-3)⟩⟩,⟨plan3508,[⟨3,0,5⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨12,8,(-4)⟩⟩,⟨plan3508,[⟨3,1,4⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3508,[⟨3,1,4⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3508,[⟨3,1,4⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3508,[⟨3,1,4⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨12,8,(-4)⟩⟩,⟨plan3508,[⟨3,1,4⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3508,[⟨3,1,4⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨11,9,(-2)⟩⟩,⟨plan3508,[⟨3,1,4⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨11,8,(-3)⟩⟩,⟨plan3508,[⟨3,2,3⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨13,6,(-7)⟩⟩]

def t6_880jobs1 : List Job := [⟨plan3508,[⟨3,2,3⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3508,[⟨3,2,3⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨12,6,(-6)⟩⟩,⟨plan3508,[⟨3,2,3⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨11,8,(-3)⟩⟩]

def t6_880jobs2 : List Job := [⟨plan3508,[⟨3,2,3⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨11,7,(-4)⟩⟩,⟨plan3508,[⟨3,2,3⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨10,9,(-1)⟩⟩]

def t6_880jobs3 : List Job := [⟨plan3508,[⟨3,2,3⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨10,8,(-2)⟩⟩,⟨plan3508,[⟨3,3,2⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨12,6,(-6)⟩⟩]

def t6_880jobs4 : List Job := [⟨plan3508,[⟨3,3,2⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨11,7,(-4)⟩⟩,⟨plan3508,[⟨3,3,2⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨11,6,(-5)⟩⟩]

def t6_880jobs5 : List Job := [⟨plan3508,[⟨3,3,2⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨10,8,(-2)⟩⟩]

def t6_880jobs6 : List Job := [⟨plan3508,[⟨3,3,2⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨10,7,(-3)⟩⟩]

def t6_880jobs7 : List Job := [⟨plan3508,[⟨3,3,2⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨9,9,0⟩⟩]

def t6_880jobs8 : List Job := [⟨plan3508,[⟨3,3,2⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨9,8,(-1)⟩⟩]

def t6_880jobs : List Job := t6_880jobs0++t6_880jobs1++t6_880jobs2++t6_880jobs3++t6_880jobs4++t6_880jobs5++t6_880jobs6++t6_880jobs7++t6_880jobs8




def t6_881root : Job := ⟨plan7426,[],none,⟨15,10,0⟩⟩
def t6_881jobs0 : List Job := [⟨plan3509,[⟨3,0,5⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3509,[⟨3,0,5⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3509,[⟨3,0,5⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3509,[⟨3,0,5⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨13,8,(-5)⟩⟩,⟨plan3509,[⟨3,0,5⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3509,[⟨3,0,5⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨12,9,(-3)⟩⟩,⟨plan3509,[⟨3,0,5⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨12,8,(-4)⟩⟩,⟨plan3509,[⟨3,1,4⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3509,[⟨3,1,4⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3509,[⟨3,1,4⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3509,[⟨3,1,4⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨12,8,(-4)⟩⟩,⟨plan3509,[⟨3,1,4⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3509,[⟨3,1,4⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨11,9,(-2)⟩⟩,⟨plan3509,[⟨3,1,4⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨11,8,(-3)⟩⟩,⟨plan3509,[⟨3,2,3⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3509,[⟨3,2,3⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3509,[⟨3,2,3⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨12,6,(-6)⟩⟩,⟨plan3509,[⟨3,2,3⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨11,8,(-3)⟩⟩,⟨plan3509,[⟨3,2,3⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨11,7,(-4)⟩⟩]

def t6_881jobs1 : List Job := [⟨plan3509,[⟨3,2,3⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨10,9,(-1)⟩⟩,⟨plan3509,[⟨3,2,3⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨10,8,(-2)⟩⟩,⟨plan3509,[⟨3,3,2⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨12,6,(-6)⟩⟩,⟨plan3509,[⟨3,3,2⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨11,7,(-4)⟩⟩,⟨plan3509,[⟨3,3,2⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨11,6,(-5)⟩⟩]

def t6_881jobs2 : List Job := [⟨plan3509,[⟨3,3,2⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨10,8,(-2)⟩⟩,⟨plan3509,[⟨3,3,2⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨10,7,(-3)⟩⟩,⟨plan3509,[⟨3,3,2⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨9,9,0⟩⟩]

def t6_881jobs3 : List Job := [⟨plan3509,[⟨3,3,2⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨9,8,(-1)⟩⟩]

def t6_881jobs : List Job := t6_881jobs0++t6_881jobs1++t6_881jobs2++t6_881jobs3




def t6_882root : Job := ⟨plan7427,[],none,⟨15,10,0⟩⟩
def t6_882jobs0 : List Job := [⟨plan7427,[],none,⟨15,10,0⟩⟩]

def t6_882jobs : List Job := t6_882jobs0




def t6_883root : Job := ⟨plan7428,[],none,⟨15,10,0⟩⟩
def t6_883jobs0 : List Job := [⟨plan5898,[⟨3,0,5⟩],(some ⟨3,0,5⟩),⟨15,10,(-5)⟩⟩,⟨plan5898,[⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨14,10,(-4)⟩⟩]

def t6_883jobs1 : List Job := [⟨plan5898,[⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨13,10,(-3)⟩⟩]

def t6_883jobs2 : List Job := [⟨plan5898,[⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨12,10,(-2)⟩⟩]

def t6_883jobs : List Job := t6_883jobs0++t6_883jobs1++t6_883jobs2



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


