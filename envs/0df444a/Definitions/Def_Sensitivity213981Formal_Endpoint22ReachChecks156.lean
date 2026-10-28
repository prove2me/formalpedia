-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks156
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks156
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:32:06.418236+00:00
-- url     : https://prove2.me/theorems/36491213-1799-4545-9f15-1ad2c1c9e008
-- title:
--   Endpoint22 Reach Checks156 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks156 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t7_68jobs0`, `ThreeBoundEndpoint22Reachable.t7_68jobs1`, `ThreeBoundEndpoint22Reachable.t7_68jobs`, `ThreeBoundEndpoint22Reachable.t7_69root`, `ThreeBoundEndpoint22Reachable.t7_69jobs0`, `ThreeBoundEndpoint22Reachable.t7_69jobs1`, `ThreeBoundEndpoint22Reachable.t7_69jobs2`, `ThreeBoundEndpoint22Reachable.t7_69jobs`, `ThreeBoundEndpoint22Reachable.t7_70root`, `ThreeBoundEndpoint22Reachable.t7_70jobs0`, `ThreeBoundEndpoint22Reachable.t7_70jobs`, `ThreeBoundEndpoint22Reachable.t7_58root`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks156.lean, lines 1–184.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans088
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans089
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

def t7_57root : Job := ⟨plan8475,[],none,⟨21,6,0⟩⟩
def t7_57jobs0 : List Job := [⟨plan8128,[⟨1,0,4⟩],(some ⟨1,0,4⟩),⟨21,6,(-4)⟩⟩,⟨plan8128,[⟨1,1,3⟩],(some ⟨1,1,3⟩),⟨20,6,(-3)⟩⟩]

def t7_57jobs1 : List Job := [⟨plan8128,[⟨1,1,4⟩],(some ⟨1,1,4⟩),⟨20,6,(-4)⟩⟩]

def t7_57jobs : List Job := t7_57jobs0++t7_57jobs1




def t7_58root : Job := ⟨plan8476,[],none,⟨21,6,0⟩⟩
def t7_58jobs0 : List Job := [⟨plan8476,[],none,⟨21,6,0⟩⟩]

def t7_58jobs : List Job := t7_58jobs0




def t7_59root : Job := ⟨plan8477,[],none,⟨21,6,0⟩⟩
def t7_59jobs0 : List Job := [⟨plan8132,[⟨1,0,4⟩],(some ⟨1,0,4⟩),⟨21,6,(-4)⟩⟩,⟨plan8132,[⟨1,1,3⟩],(some ⟨1,1,3⟩),⟨20,6,(-3)⟩⟩]

def t7_59jobs1 : List Job := [⟨plan8132,[⟨1,1,4⟩],(some ⟨1,1,4⟩),⟨20,6,(-4)⟩⟩]

def t7_59jobs : List Job := t7_59jobs0++t7_59jobs1




def t7_60root : Job := ⟨plan8478,[],none,⟨21,6,0⟩⟩
def t7_60jobs0 : List Job := [⟨plan8133,[⟨1,0,4⟩],(some ⟨1,0,4⟩),⟨21,6,(-4)⟩⟩,⟨plan8133,[⟨1,1,3⟩],(some ⟨1,1,3⟩),⟨20,6,(-3)⟩⟩]

def t7_60jobs1 : List Job := [⟨plan8133,[⟨1,1,4⟩],(some ⟨1,1,4⟩),⟨20,6,(-4)⟩⟩]

def t7_60jobs : List Job := t7_60jobs0++t7_60jobs1




def t7_61root : Job := ⟨plan8479,[],none,⟨21,6,0⟩⟩
def t7_61jobs0 : List Job := [⟨plan8479,[],none,⟨21,6,0⟩⟩]

def t7_61jobs : List Job := t7_61jobs0




def t7_62root : Job := ⟨plan8570,[],none,⟨21,10,0⟩⟩
def t7_62jobs0 : List Job := [⟨plan8570,[],none,⟨21,10,0⟩⟩]

def t7_62jobs : List Job := t7_62jobs0




def t7_63root : Job := ⟨plan8571,[],none,⟨21,10,0⟩⟩
def t7_63jobs0 : List Job := [⟨plan8571,[],none,⟨21,10,0⟩⟩]

def t7_63jobs : List Job := t7_63jobs0




def t7_64root : Job := ⟨plan8572,[],none,⟨21,10,0⟩⟩
def t7_64jobs0 : List Job := [⟨plan8572,[],none,⟨21,10,0⟩⟩]

def t7_64jobs : List Job := t7_64jobs0




def t7_65root : Job := ⟨plan8573,[],none,⟨21,10,0⟩⟩
def t7_65jobs0 : List Job := [⟨plan8188,[⟨1,0,5⟩],(some ⟨1,0,5⟩),⟨21,10,(-5)⟩⟩]

def t7_65jobs1 : List Job := [⟨plan8188,[⟨1,1,4⟩],(some ⟨1,1,4⟩),⟨20,10,(-4)⟩⟩]

def t7_65jobs2 : List Job := [⟨plan8188,[⟨1,1,5⟩],(some ⟨1,1,5⟩),⟨20,10,(-5)⟩⟩]

def t7_65jobs : List Job := t7_65jobs0++t7_65jobs1++t7_65jobs2




def t7_66root : Job := ⟨plan8574,[],none,⟨21,10,0⟩⟩
def t7_66jobs0 : List Job := [⟨plan8189,[⟨1,0,5⟩],(some ⟨1,0,5⟩),⟨21,10,(-5)⟩⟩,⟨plan8189,[⟨1,1,4⟩],(some ⟨1,1,4⟩),⟨20,10,(-4)⟩⟩]

def t7_66jobs1 : List Job := [⟨plan8189,[⟨1,1,5⟩],(some ⟨1,1,5⟩),⟨20,10,(-5)⟩⟩]

def t7_66jobs : List Job := t7_66jobs0++t7_66jobs1




def t7_67root : Job := ⟨plan8575,[],none,⟨21,10,0⟩⟩
def t7_67jobs0 : List Job := [⟨plan8575,[],none,⟨21,10,0⟩⟩]

def t7_67jobs : List Job := t7_67jobs0




def t7_68root : Job := ⟨plan8576,[],none,⟨21,10,0⟩⟩
def t7_68jobs0 : List Job := [⟨plan8193,[⟨1,0,5⟩],(some ⟨1,0,5⟩),⟨21,10,(-5)⟩⟩,⟨plan8193,[⟨1,1,4⟩],(some ⟨1,1,4⟩),⟨20,10,(-4)⟩⟩]

def t7_68jobs1 : List Job := [⟨plan8193,[⟨1,1,5⟩],(some ⟨1,1,5⟩),⟨20,10,(-5)⟩⟩]

def t7_68jobs : List Job := t7_68jobs0++t7_68jobs1




def t7_69root : Job := ⟨plan8577,[],none,⟨21,10,0⟩⟩
def t7_69jobs0 : List Job := [⟨plan8194,[⟨1,0,5⟩],(some ⟨1,0,5⟩),⟨21,10,(-5)⟩⟩]

def t7_69jobs1 : List Job := [⟨plan8194,[⟨1,1,4⟩],(some ⟨1,1,4⟩),⟨20,10,(-4)⟩⟩]

def t7_69jobs2 : List Job := [⟨plan8194,[⟨1,1,5⟩],(some ⟨1,1,5⟩),⟨20,10,(-5)⟩⟩]

def t7_69jobs : List Job := t7_69jobs0++t7_69jobs1++t7_69jobs2




def t7_70root : Job := ⟨plan8578,[],none,⟨21,10,0⟩⟩
def t7_70jobs0 : List Job := [⟨plan8578,[],none,⟨21,10,0⟩⟩]

def t7_70jobs : List Job := t7_70jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


