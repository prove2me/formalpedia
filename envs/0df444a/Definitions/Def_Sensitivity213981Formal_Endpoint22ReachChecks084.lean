-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks084
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks084
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:25:58.151235+00:00
-- url     : https://prove2.me/theorems/6020d16b-c3ab-4706-a329-0da60c444c07
-- title:
--   Endpoint22 Reach Checks084 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks084 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_680jobs1`, `ThreeBoundEndpoint22Reachable.t6_680jobs2`, `ThreeBoundEndpoint22Reachable.t6_680jobs3`, `ThreeBoundEndpoint22Reachable.t6_680jobs4`, `ThreeBoundEndpoint22Reachable.t6_680jobs5`, `ThreeBoundEndpoint22Reachable.t6_680jobs6`, `ThreeBoundEndpoint22Reachable.t6_680jobs7`, `ThreeBoundEndpoint22Reachable.t6_680jobs8`, `ThreeBoundEndpoint22Reachable.t6_680jobs9`, `ThreeBoundEndpoint22Reachable.t6_680jobs10`, `ThreeBoundEndpoint22Reachable.t6_680jobs`, `ThreeBoundEndpoint22Reachable.t6_680root`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks084.lean, lines 1–76.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
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

def t6_680root : Job := ⟨plan6933,[],none,⟨15,6,0⟩⟩
def t6_680jobs0 : List Job := [⟨plan3364,[⟨2,0,4⟩,⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨15,3,(-7)⟩⟩,⟨plan3364,[⟨2,0,4⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨14,4,(-5)⟩⟩,⟨plan3364,[⟨2,0,4⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3364,[⟨2,0,4⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨13,5,(-3)⟩⟩,⟨plan3364,[⟨2,0,4⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨13,4,(-4)⟩⟩,⟨plan3364,[⟨2,0,4⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3364,[⟨2,1,3⟩,⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3364,[⟨2,1,3⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨13,4,(-4)⟩⟩,⟨plan3364,[⟨2,1,3⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3364,[⟨2,1,3⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨12,5,(-2)⟩⟩,⟨plan3364,[⟨2,1,3⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨12,4,(-3)⟩⟩]

def t6_680jobs1 : List Job := [⟨plan3364,[⟨2,1,3⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨12,3,(-4)⟩⟩,⟨plan3364,[⟨2,1,4⟩,⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨14,3,(-7)⟩⟩,⟨plan3364,[⟨2,1,4⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨13,4,(-5)⟩⟩,⟨plan3364,[⟨2,1,4⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨13,3,(-6)⟩⟩,⟨plan3364,[⟨2,1,4⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨12,5,(-3)⟩⟩]

def t6_680jobs2 : List Job := [⟨plan3364,[⟨2,1,4⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨12,4,(-4)⟩⟩,⟨plan3364,[⟨2,1,4⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨12,3,(-5)⟩⟩,⟨plan3364,[⟨2,2,2⟩,⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨13,3,(-5)⟩⟩]

def t6_680jobs3 : List Job := [⟨plan3364,[⟨2,2,2⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨12,4,(-3)⟩⟩,⟨plan3364,[⟨2,2,2⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨12,3,(-4)⟩⟩]

def t6_680jobs4 : List Job := [⟨plan3364,[⟨2,2,2⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨11,5,(-1)⟩⟩]

def t6_680jobs5 : List Job := [⟨plan3364,[⟨2,2,2⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨11,4,(-2)⟩⟩]

def t6_680jobs6 : List Job := [⟨plan3364,[⟨2,2,2⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨11,3,(-3)⟩⟩,⟨plan3364,[⟨2,2,3⟩,⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨13,3,(-6)⟩⟩]

def t6_680jobs7 : List Job := [⟨plan3364,[⟨2,2,3⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨12,4,(-4)⟩⟩,⟨plan3364,[⟨2,2,3⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨12,3,(-5)⟩⟩]

def t6_680jobs8 : List Job := [⟨plan3364,[⟨2,2,3⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨11,5,(-2)⟩⟩]

def t6_680jobs9 : List Job := [⟨plan3364,[⟨2,2,3⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨11,4,(-3)⟩⟩]

def t6_680jobs10 : List Job := [⟨plan3364,[⟨2,2,3⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨11,3,(-4)⟩⟩]

def t6_680jobs : List Job := t6_680jobs0++t6_680jobs1++t6_680jobs2++t6_680jobs3++t6_680jobs4++t6_680jobs5++t6_680jobs6++t6_680jobs7++t6_680jobs8++t6_680jobs9++t6_680jobs10




def t6_681root : Job := ⟨plan6934,[],none,⟨15,6,0⟩⟩
def t6_681jobs0 : List Job := [⟨plan5673,[⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5673,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨14,6,(-3)⟩⟩,⟨plan5673,[⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨14,6,(-4)⟩⟩,⟨plan5673,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨13,6,(-2)⟩⟩]

def t6_681jobs1 : List Job := [⟨plan5673,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨13,6,(-3)⟩⟩]

def t6_681jobs : List Job := t6_681jobs0++t6_681jobs1




def t6_682root : Job := ⟨plan6935,[],none,⟨15,6,0⟩⟩
def t6_682jobs0 : List Job := [⟨plan3366,[⟨2,0,4⟩,⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨15,3,(-7)⟩⟩,⟨plan3366,[⟨2,0,4⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨14,4,(-5)⟩⟩,⟨plan3366,[⟨2,0,4⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3366,[⟨2,0,4⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨13,5,(-3)⟩⟩,⟨plan3366,[⟨2,0,4⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨13,4,(-4)⟩⟩,⟨plan3366,[⟨2,0,4⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3366,[⟨2,1,3⟩,⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3366,[⟨2,1,3⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨13,4,(-4)⟩⟩,⟨plan3366,[⟨2,1,3⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3366,[⟨2,1,3⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨12,5,(-2)⟩⟩,⟨plan3366,[⟨2,1,3⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨12,4,(-3)⟩⟩]

def t6_682jobs1 : List Job := [⟨plan3366,[⟨2,1,3⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨12,3,(-4)⟩⟩,⟨plan3366,[⟨2,1,4⟩,⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨14,3,(-7)⟩⟩,⟨plan3366,[⟨2,1,4⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨13,4,(-5)⟩⟩,⟨plan3366,[⟨2,1,4⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨13,3,(-6)⟩⟩,⟨plan3366,[⟨2,1,4⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨12,5,(-3)⟩⟩,⟨plan3366,[⟨2,1,4⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨12,4,(-4)⟩⟩]

def t6_682jobs2 : List Job := [⟨plan3366,[⟨2,1,4⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨12,3,(-5)⟩⟩,⟨plan3366,[⟨2,2,2⟩,⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3366,[⟨2,2,2⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨12,4,(-3)⟩⟩,⟨plan3366,[⟨2,2,2⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨12,3,(-4)⟩⟩]

def t6_682jobs3 : List Job := [⟨plan3366,[⟨2,2,2⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨11,5,(-1)⟩⟩,⟨plan3366,[⟨2,2,2⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨11,4,(-2)⟩⟩,⟨plan3366,[⟨2,2,2⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨11,3,(-3)⟩⟩]

def t6_682jobs4 : List Job := [⟨plan3366,[⟨2,2,3⟩,⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨13,3,(-6)⟩⟩,⟨plan3366,[⟨2,2,3⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨12,4,(-4)⟩⟩,⟨plan3366,[⟨2,2,3⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨12,3,(-5)⟩⟩,⟨plan3366,[⟨2,2,3⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨11,5,(-2)⟩⟩]

def t6_682jobs5 : List Job := [⟨plan3366,[⟨2,2,3⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨11,4,(-3)⟩⟩,⟨plan3366,[⟨2,2,3⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨11,3,(-4)⟩⟩]

def t6_682jobs : List Job := t6_682jobs0++t6_682jobs1++t6_682jobs2++t6_682jobs3++t6_682jobs4++t6_682jobs5



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


