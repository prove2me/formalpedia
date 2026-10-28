-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks020
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks020
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:26:04.781445+00:00
-- url     : https://prove2.me/theorems/53df6326-3faa-49a5-87d8-19d35c507263
-- title:
--   Endpoint22 Reach Checks020 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks020 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t5_755jobs`, `ThreeBoundEndpoint22Reachable.t5_756root`, `ThreeBoundEndpoint22Reachable.t5_756jobs0`, `ThreeBoundEndpoint22Reachable.t5_756jobs1`, `ThreeBoundEndpoint22Reachable.t5_756jobs`, `ThreeBoundEndpoint22Reachable.t5_757root`, `ThreeBoundEndpoint22Reachable.t5_757jobs0`, `ThreeBoundEndpoint22Reachable.t5_757jobs1`, `ThreeBoundEndpoint22Reachable.t5_757jobs2`, `ThreeBoundEndpoint22Reachable.t5_757jobs3`, `ThreeBoundEndpoint22Reachable.t5_757jobs`, `ThreeBoundEndpoint22Reachable.t5_758root`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks020.lean, lines 1–106.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans040
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans044
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

def t5_755root : Job := ⟨plan3936,[],none,⟨10,1,0⟩⟩
def t5_755jobs0 : List Job := [⟨plan2650,[⟨2,0,2⟩],(some ⟨2,0,2⟩),⟨10,1,(-2)⟩⟩,⟨plan2650,[⟨2,1,1⟩],(some ⟨2,1,1⟩),⟨9,1,(-1)⟩⟩,⟨plan2650,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨9,1,(-2)⟩⟩,⟨plan2650,[⟨2,2,0⟩],(some ⟨2,2,0⟩),⟨8,1,0⟩⟩]

def t5_755jobs1 : List Job := [⟨plan2650,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨8,1,(-1)⟩⟩,⟨plan2650,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,1,(-2)⟩⟩]

def t5_755jobs : List Job := t5_755jobs0++t5_755jobs1




def t5_756root : Job := ⟨plan4279,[],none,⟨10,3,0⟩⟩
def t5_756jobs0 : List Job := [⟨plan2812,[⟨2,0,3⟩],(some ⟨2,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2812,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨9,3,(-2)⟩⟩,⟨plan2812,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨9,3,(-3)⟩⟩]

def t5_756jobs1 : List Job := [⟨plan2812,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨8,3,(-1)⟩⟩,⟨plan2812,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,3,(-2)⟩⟩]

def t5_756jobs : List Job := t5_756jobs0++t5_756jobs1




def t5_757root : Job := ⟨plan4280,[],none,⟨10,3,0⟩⟩
def t5_757jobs0 : List Job := [⟨plan2813,[⟨2,0,3⟩],(some ⟨2,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2813,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨9,3,(-2)⟩⟩]

def t5_757jobs1 : List Job := [⟨plan2813,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨9,3,(-3)⟩⟩]

def t5_757jobs2 : List Job := [⟨plan2813,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨8,3,(-1)⟩⟩]

def t5_757jobs3 : List Job := [⟨plan2813,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,3,(-2)⟩⟩]

def t5_757jobs : List Job := t5_757jobs0++t5_757jobs1++t5_757jobs2++t5_757jobs3




def t5_758root : Job := ⟨plan4281,[],none,⟨10,3,0⟩⟩
def t5_758jobs0 : List Job := [⟨plan2814,[⟨2,0,3⟩],(some ⟨2,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2814,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨9,3,(-2)⟩⟩]

def t5_758jobs1 : List Job := [⟨plan2814,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨9,3,(-3)⟩⟩]

def t5_758jobs2 : List Job := [⟨plan2814,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨8,3,(-1)⟩⟩]

def t5_758jobs3 : List Job := [⟨plan2814,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,3,(-2)⟩⟩]

def t5_758jobs : List Job := t5_758jobs0++t5_758jobs1++t5_758jobs2++t5_758jobs3




def t5_759root : Job := ⟨plan4282,[],none,⟨10,3,0⟩⟩
def t5_759jobs0 : List Job := [⟨plan2815,[⟨2,0,3⟩],(some ⟨2,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2815,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨9,3,(-2)⟩⟩]

def t5_759jobs1 : List Job := [⟨plan2815,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨9,3,(-3)⟩⟩]

def t5_759jobs2 : List Job := [⟨plan2815,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨8,3,(-1)⟩⟩]

def t5_759jobs3 : List Job := [⟨plan2815,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,3,(-2)⟩⟩]

def t5_759jobs : List Job := t5_759jobs0++t5_759jobs1++t5_759jobs2++t5_759jobs3




def t5_760root : Job := ⟨plan4283,[],none,⟨10,3,0⟩⟩
def t5_760jobs0 : List Job := [⟨plan2816,[⟨2,0,3⟩],(some ⟨2,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2816,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨9,3,(-2)⟩⟩]

def t5_760jobs1 : List Job := [⟨plan2816,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨9,3,(-3)⟩⟩]

def t5_760jobs2 : List Job := [⟨plan2816,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨8,3,(-1)⟩⟩]

def t5_760jobs3 : List Job := [⟨plan2816,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,3,(-2)⟩⟩]

def t5_760jobs : List Job := t5_760jobs0++t5_760jobs1++t5_760jobs2++t5_760jobs3



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


