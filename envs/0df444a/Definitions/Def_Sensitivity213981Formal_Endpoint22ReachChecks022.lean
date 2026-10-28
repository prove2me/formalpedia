-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks022
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks022
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:23:36.167903+00:00
-- url     : https://prove2.me/theorems/0558fb77-bb41-4c85-937a-65c07023311c
-- title:
--   Endpoint22 Reach Checks022 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks022 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t5_798jobs`, `ThreeBoundEndpoint22Reachable.t5_799root`, `ThreeBoundEndpoint22Reachable.t5_799jobs0`, `ThreeBoundEndpoint22Reachable.t5_799jobs`, `ThreeBoundEndpoint22Reachable.t5_800root`, `ThreeBoundEndpoint22Reachable.t5_800jobs0`, `ThreeBoundEndpoint22Reachable.t5_800jobs`, `ThreeBoundEndpoint22Reachable.t5_801root`, `ThreeBoundEndpoint22Reachable.t5_801jobs0`, `ThreeBoundEndpoint22Reachable.t5_789root`, `ThreeBoundEndpoint22Reachable.t5_801jobs`, `ThreeBoundEndpoint22Reachable.t5_802root`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks022.lean, lines 1–218.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans041
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans044
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans048
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

def t5_788root : Job := ⟨plan4683,[],none,⟨10,6,0⟩⟩
def t5_788jobs0 : List Job := [⟨plan4683,[],none,⟨10,6,0⟩⟩]

def t5_788jobs : List Job := t5_788jobs0




def t5_789root : Job := ⟨plan4684,[],none,⟨10,6,0⟩⟩
def t5_789jobs0 : List Job := [⟨plan4684,[],none,⟨10,6,0⟩⟩]

def t5_789jobs : List Job := t5_789jobs0




def t5_790root : Job := ⟨plan3938,[],none,⟨10,1,0⟩⟩
def t5_790jobs0 : List Job := [⟨plan3938,[],none,⟨10,1,0⟩⟩]

def t5_790jobs : List Job := t5_790jobs0




def t5_791root : Job := ⟨plan4290,[],none,⟨10,3,0⟩⟩
def t5_791jobs0 : List Job := [⟨plan2825,[⟨2,0,3⟩],(some ⟨2,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2825,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨9,3,(-2)⟩⟩,⟨plan2825,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨9,3,(-3)⟩⟩]

def t5_791jobs1 : List Job := [⟨plan2825,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨8,3,(-1)⟩⟩]

def t5_791jobs2 : List Job := [⟨plan2825,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,3,(-2)⟩⟩]

def t5_791jobs : List Job := t5_791jobs0++t5_791jobs1++t5_791jobs2




def t5_792root : Job := ⟨plan4291,[],none,⟨10,3,0⟩⟩
def t5_792jobs0 : List Job := [⟨plan2826,[⟨2,0,3⟩],(some ⟨2,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2826,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨9,3,(-2)⟩⟩]

def t5_792jobs1 : List Job := [⟨plan2826,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨9,3,(-3)⟩⟩]

def t5_792jobs2 : List Job := [⟨plan2826,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨8,3,(-1)⟩⟩]

def t5_792jobs3 : List Job := [⟨plan2826,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,3,(-2)⟩⟩]

def t5_792jobs : List Job := t5_792jobs0++t5_792jobs1++t5_792jobs2++t5_792jobs3




def t5_793root : Job := ⟨plan4292,[],none,⟨10,3,0⟩⟩
def t5_793jobs0 : List Job := [⟨plan2827,[⟨2,0,3⟩],(some ⟨2,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2827,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨9,3,(-2)⟩⟩,⟨plan2827,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨9,3,(-3)⟩⟩]

def t5_793jobs1 : List Job := [⟨plan2827,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨8,3,(-1)⟩⟩]

def t5_793jobs2 : List Job := [⟨plan2827,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,3,(-2)⟩⟩]

def t5_793jobs : List Job := t5_793jobs0++t5_793jobs1++t5_793jobs2




def t5_794root : Job := ⟨plan4685,[],none,⟨10,6,0⟩⟩
def t5_794jobs0 : List Job := [⟨plan4685,[],none,⟨10,6,0⟩⟩]

def t5_794jobs : List Job := t5_794jobs0




def t5_795root : Job := ⟨plan4686,[],none,⟨10,6,0⟩⟩
def t5_795jobs0 : List Job := [⟨plan3004,[⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨10,6,(-4)⟩⟩,⟨plan3004,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨9,6,(-3)⟩⟩]

def t5_795jobs1 : List Job := [⟨plan3004,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,6,(-2)⟩⟩]

def t5_795jobs : List Job := t5_795jobs0++t5_795jobs1




def t5_796root : Job := ⟨plan4687,[],none,⟨10,6,0⟩⟩
def t5_796jobs0 : List Job := [⟨plan4687,[],none,⟨10,6,0⟩⟩]

def t5_796jobs : List Job := t5_796jobs0




def t5_797root : Job := ⟨plan4688,[],none,⟨10,6,0⟩⟩
def t5_797jobs0 : List Job := [⟨plan4688,[],none,⟨10,6,0⟩⟩]

def t5_797jobs : List Job := t5_797jobs0




def t5_798root : Job := ⟨plan4293,[],none,⟨10,3,0⟩⟩
def t5_798jobs0 : List Job := [⟨plan4293,[],none,⟨10,3,0⟩⟩]

def t5_798jobs : List Job := t5_798jobs0




def t5_799root : Job := ⟨plan4689,[],none,⟨10,6,0⟩⟩
def t5_799jobs0 : List Job := [⟨plan4689,[],none,⟨10,6,0⟩⟩]

def t5_799jobs : List Job := t5_799jobs0




def t5_800root : Job := ⟨plan4690,[],none,⟨10,6,0⟩⟩
def t5_800jobs0 : List Job := [⟨plan4690,[],none,⟨10,6,0⟩⟩]

def t5_800jobs : List Job := t5_800jobs0




def t5_801root : Job := ⟨plan4691,[],none,⟨10,6,0⟩⟩
def t5_801jobs0 : List Job := [⟨plan4691,[],none,⟨10,6,0⟩⟩]

def t5_801jobs : List Job := t5_801jobs0




def t5_802root : Job := ⟨plan4692,[],none,⟨10,6,0⟩⟩
def t5_802jobs0 : List Job := [⟨plan4692,[],none,⟨10,6,0⟩⟩]

def t5_802jobs : List Job := t5_802jobs0




def t5_803root : Job := ⟨plan4693,[],none,⟨10,6,0⟩⟩
def t5_803jobs0 : List Job := [⟨plan3012,[⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨10,6,(-4)⟩⟩,⟨plan3012,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨9,6,(-3)⟩⟩]

def t5_803jobs1 : List Job := [⟨plan3012,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,6,(-2)⟩⟩]

def t5_803jobs : List Job := t5_803jobs0++t5_803jobs1




def t5_804root : Job := ⟨plan4694,[],none,⟨10,6,0⟩⟩
def t5_804jobs0 : List Job := [⟨plan4694,[],none,⟨10,6,0⟩⟩]

def t5_804jobs : List Job := t5_804jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


