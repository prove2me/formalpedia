-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks009
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks009
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:22:15.805408+00:00
-- url     : https://prove2.me/theorems/e45c237d-3908-408a-83be-1c970f288c79
-- title:
--   Endpoint22 Reach Checks009 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks009 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t5_405jobs0`, `ThreeBoundEndpoint22Reachable.t5_405jobs`, `ThreeBoundEndpoint22Reachable.t5_406root`, `ThreeBoundEndpoint22Reachable.t5_406jobs0`, `ThreeBoundEndpoint22Reachable.t5_406jobs`, `ThreeBoundEndpoint22Reachable.t5_407root`, `ThreeBoundEndpoint22Reachable.t5_407jobs0`, `ThreeBoundEndpoint22Reachable.t5_407jobs`, `ThreeBoundEndpoint22Reachable.t5_408root`, `ThreeBoundEndpoint22Reachable.t5_393root`, `ThreeBoundEndpoint22Reachable.t5_408jobs0`, `ThreeBoundEndpoint22Reachable.t5_408jobs1`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks009.lean, lines 1–298.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans038
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans040
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans043
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

def t5_392root : Job := ⟨plan4146,[],none,⟨10,3,0⟩⟩
def t5_392jobs0 : List Job := [⟨plan4146,[],none,⟨10,3,0⟩⟩]

def t5_392jobs : List Job := t5_392jobs0




def t5_393root : Job := ⟨plan4147,[],none,⟨10,3,0⟩⟩
def t5_393jobs0 : List Job := [⟨plan4147,[],none,⟨10,3,0⟩⟩]

def t5_393jobs : List Job := t5_393jobs0




def t5_394root : Job := ⟨plan3864,[],none,⟨10,1,0⟩⟩
def t5_394jobs0 : List Job := [⟨plan3864,[],none,⟨10,1,0⟩⟩]

def t5_394jobs : List Job := t5_394jobs0




def t5_395root : Job := ⟨plan4148,[],none,⟨10,3,0⟩⟩
def t5_395jobs0 : List Job := [⟨plan4148,[],none,⟨10,3,0⟩⟩]

def t5_395jobs : List Job := t5_395jobs0




def t5_396root : Job := ⟨plan4149,[],none,⟨10,3,0⟩⟩
def t5_396jobs0 : List Job := [⟨plan4149,[],none,⟨10,3,0⟩⟩]

def t5_396jobs : List Job := t5_396jobs0




def t5_397root : Job := ⟨plan4150,[],none,⟨10,3,0⟩⟩
def t5_397jobs0 : List Job := [⟨plan4150,[],none,⟨10,3,0⟩⟩]

def t5_397jobs : List Job := t5_397jobs0




def t5_398root : Job := ⟨plan4151,[],none,⟨10,3,0⟩⟩
def t5_398jobs0 : List Job := [⟨plan4151,[],none,⟨10,3,0⟩⟩]

def t5_398jobs : List Job := t5_398jobs0




def t5_399root : Job := ⟨plan4152,[],none,⟨10,3,0⟩⟩
def t5_399jobs0 : List Job := [⟨plan4152,[],none,⟨10,3,0⟩⟩]

def t5_399jobs : List Job := t5_399jobs0




def t5_400root : Job := ⟨plan4153,[],none,⟨10,3,0⟩⟩
def t5_400jobs0 : List Job := [⟨plan4153,[],none,⟨10,3,0⟩⟩]

def t5_400jobs : List Job := t5_400jobs0




def t5_401root : Job := ⟨plan4154,[],none,⟨10,3,0⟩⟩
def t5_401jobs0 : List Job := [⟨plan4154,[],none,⟨10,3,0⟩⟩]

def t5_401jobs : List Job := t5_401jobs0




def t5_402root : Job := ⟨plan4155,[],none,⟨10,3,0⟩⟩
def t5_402jobs0 : List Job := [⟨plan4155,[],none,⟨10,3,0⟩⟩]

def t5_402jobs : List Job := t5_402jobs0




def t5_403root : Job := ⟨plan3667,[],none,⟨10,0,0⟩⟩
def t5_403jobs0 : List Job := [⟨plan3667,[],none,⟨10,0,0⟩⟩]

def t5_403jobs : List Job := t5_403jobs0




def t5_404root : Job := ⟨plan3717,[],none,⟨10,0,0⟩⟩
def t5_404jobs0 : List Job := [⟨plan3717,[],none,⟨10,0,0⟩⟩]

def t5_404jobs : List Job := t5_404jobs0




def t5_405root : Job := ⟨plan3718,[],none,⟨10,0,0⟩⟩
def t5_405jobs0 : List Job := [⟨plan3718,[],none,⟨10,0,0⟩⟩]

def t5_405jobs : List Job := t5_405jobs0




def t5_406root : Job := ⟨plan3719,[],none,⟨10,0,0⟩⟩
def t5_406jobs0 : List Job := [⟨plan3719,[],none,⟨10,0,0⟩⟩]

def t5_406jobs : List Job := t5_406jobs0




def t5_407root : Job := ⟨plan3865,[],none,⟨10,1,0⟩⟩
def t5_407jobs0 : List Job := [⟨plan3865,[],none,⟨10,1,0⟩⟩]

def t5_407jobs : List Job := t5_407jobs0




def t5_408root : Job := ⟨plan3866,[],none,⟨10,1,0⟩⟩
def t5_408jobs0 : List Job := [⟨plan2631,[⟨1,0,2⟩],(some ⟨1,0,2⟩),⟨10,1,(-2)⟩⟩,⟨plan2631,[⟨1,1,1⟩],(some ⟨1,1,1⟩),⟨9,1,(-1)⟩⟩]

def t5_408jobs1 : List Job := [⟨plan2631,[⟨1,1,2⟩],(some ⟨1,1,2⟩),⟨9,1,(-2)⟩⟩]

def t5_408jobs : List Job := t5_408jobs0++t5_408jobs1




def t5_409root : Job := ⟨plan3867,[],none,⟨10,1,0⟩⟩
def t5_409jobs0 : List Job := [⟨plan3867,[],none,⟨10,1,0⟩⟩]

def t5_409jobs : List Job := t5_409jobs0




def t5_410root : Job := ⟨plan3868,[],none,⟨10,1,0⟩⟩
def t5_410jobs0 : List Job := [⟨plan3868,[],none,⟨10,1,0⟩⟩]

def t5_410jobs : List Job := t5_410jobs0




def t5_411root : Job := ⟨plan3869,[],none,⟨10,1,0⟩⟩
def t5_411jobs0 : List Job := [⟨plan2634,[⟨1,0,2⟩],(some ⟨1,0,2⟩),⟨10,1,(-2)⟩⟩,⟨plan2634,[⟨1,1,1⟩],(some ⟨1,1,1⟩),⟨9,1,(-1)⟩⟩]

def t5_411jobs1 : List Job := [⟨plan2634,[⟨1,1,2⟩],(some ⟨1,1,2⟩),⟨9,1,(-2)⟩⟩]

def t5_411jobs : List Job := t5_411jobs0++t5_411jobs1




def t5_412root : Job := ⟨plan3870,[],none,⟨10,1,0⟩⟩
def t5_412jobs0 : List Job := [⟨plan3870,[],none,⟨10,1,0⟩⟩]

def t5_412jobs : List Job := t5_412jobs0




def t5_413root : Job := ⟨plan4156,[],none,⟨10,3,0⟩⟩
def t5_413jobs0 : List Job := [⟨plan4156,[],none,⟨10,3,0⟩⟩]

def t5_413jobs : List Job := t5_413jobs0




def t5_414root : Job := ⟨plan4157,[],none,⟨10,3,0⟩⟩
def t5_414jobs0 : List Job := [⟨plan2769,[⟨1,0,3⟩],(some ⟨1,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2769,[⟨1,1,2⟩],(some ⟨1,1,2⟩),⟨9,3,(-2)⟩⟩]

def t5_414jobs1 : List Job := [⟨plan2769,[⟨1,1,3⟩],(some ⟨1,1,3⟩),⟨9,3,(-3)⟩⟩]

def t5_414jobs : List Job := t5_414jobs0++t5_414jobs1




def t5_415root : Job := ⟨plan4158,[],none,⟨10,3,0⟩⟩
def t5_415jobs0 : List Job := [⟨plan2770,[⟨1,0,3⟩],(some ⟨1,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2770,[⟨1,1,2⟩],(some ⟨1,1,2⟩),⟨9,3,(-2)⟩⟩]

def t5_415jobs1 : List Job := [⟨plan2770,[⟨1,1,3⟩],(some ⟨1,1,3⟩),⟨9,3,(-3)⟩⟩]

def t5_415jobs : List Job := t5_415jobs0++t5_415jobs1




def t5_416root : Job := ⟨plan4159,[],none,⟨10,3,0⟩⟩
def t5_416jobs0 : List Job := [⟨plan2771,[⟨1,0,3⟩],(some ⟨1,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2771,[⟨1,1,2⟩],(some ⟨1,1,2⟩),⟨9,3,(-2)⟩⟩]

def t5_416jobs1 : List Job := [⟨plan2771,[⟨1,1,3⟩],(some ⟨1,1,3⟩),⟨9,3,(-3)⟩⟩]

def t5_416jobs : List Job := t5_416jobs0++t5_416jobs1



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


