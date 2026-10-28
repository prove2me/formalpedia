-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks021
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks021
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:25:51.450719+00:00
-- url     : https://prove2.me/theorems/deb6c1a4-e631-4eec-b59c-778f63fa9300
-- title:
--   Endpoint22 Reach Checks021 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks021 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t5_773root`, `ThreeBoundEndpoint22Reachable.t5_773jobs0`, `ThreeBoundEndpoint22Reachable.t5_773jobs`, `ThreeBoundEndpoint22Reachable.t5_774root`, `ThreeBoundEndpoint22Reachable.t5_774jobs0`, `ThreeBoundEndpoint22Reachable.t5_761jobs`, `ThreeBoundEndpoint22Reachable.t5_774jobs`, `ThreeBoundEndpoint22Reachable.t5_775root`, `ThreeBoundEndpoint22Reachable.t5_775jobs0`, `ThreeBoundEndpoint22Reachable.t5_775jobs`, `ThreeBoundEndpoint22Reachable.t5_776root`, `ThreeBoundEndpoint22Reachable.t5_776jobs0`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks021.lean, lines 1–322.

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

def t5_761root : Job := ⟨plan4284,[],none,⟨10,3,0⟩⟩
def t5_761jobs0 : List Job := [⟨plan2817,[⟨2,0,3⟩],(some ⟨2,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2817,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨9,3,(-2)⟩⟩,⟨plan2817,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨9,3,(-3)⟩⟩]

def t5_761jobs1 : List Job := [⟨plan2817,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨8,3,(-1)⟩⟩,⟨plan2817,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,3,(-2)⟩⟩]

def t5_761jobs : List Job := t5_761jobs0++t5_761jobs1




def t5_762root : Job := ⟨plan3937,[],none,⟨10,1,0⟩⟩
def t5_762jobs0 : List Job := [⟨plan3937,[],none,⟨10,1,0⟩⟩]

def t5_762jobs : List Job := t5_762jobs0




def t5_763root : Job := ⟨plan4285,[],none,⟨10,3,0⟩⟩
def t5_763jobs0 : List Job := [⟨plan4285,[],none,⟨10,3,0⟩⟩]

def t5_763jobs : List Job := t5_763jobs0




def t5_764root : Job := ⟨plan4286,[],none,⟨10,3,0⟩⟩
def t5_764jobs0 : List Job := [⟨plan2820,[⟨2,0,3⟩],(some ⟨2,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2820,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨9,3,(-2)⟩⟩,⟨plan2820,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨9,3,(-3)⟩⟩,⟨plan2820,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨8,3,(-1)⟩⟩]

def t5_764jobs1 : List Job := [⟨plan2820,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,3,(-2)⟩⟩]

def t5_764jobs : List Job := t5_764jobs0++t5_764jobs1




def t5_765root : Job := ⟨plan4287,[],none,⟨10,3,0⟩⟩
def t5_765jobs0 : List Job := [⟨plan4287,[],none,⟨10,3,0⟩⟩]

def t5_765jobs : List Job := t5_765jobs0




def t5_766root : Job := ⟨plan4288,[],none,⟨10,3,0⟩⟩
def t5_766jobs0 : List Job := [⟨plan4288,[],none,⟨10,3,0⟩⟩]

def t5_766jobs : List Job := t5_766jobs0




def t5_767root : Job := ⟨plan4663,[],none,⟨10,6,0⟩⟩
def t5_767jobs0 : List Job := [⟨plan4663,[],none,⟨10,6,0⟩⟩]

def t5_767jobs : List Job := t5_767jobs0




def t5_768root : Job := ⟨plan4664,[],none,⟨10,6,0⟩⟩
def t5_768jobs0 : List Job := [⟨plan4664,[],none,⟨10,6,0⟩⟩]

def t5_768jobs : List Job := t5_768jobs0




def t5_769root : Job := ⟨plan4665,[],none,⟨10,6,0⟩⟩
def t5_769jobs0 : List Job := [⟨plan4665,[],none,⟨10,6,0⟩⟩]

def t5_769jobs : List Job := t5_769jobs0




def t5_770root : Job := ⟨plan4666,[],none,⟨10,6,0⟩⟩
def t5_770jobs0 : List Job := [⟨plan4666,[],none,⟨10,6,0⟩⟩]

def t5_770jobs : List Job := t5_770jobs0




def t5_771root : Job := ⟨plan4667,[],none,⟨10,6,0⟩⟩
def t5_771jobs0 : List Job := [⟨plan4667,[],none,⟨10,6,0⟩⟩]

def t5_771jobs : List Job := t5_771jobs0




def t5_772root : Job := ⟨plan4668,[],none,⟨10,6,0⟩⟩
def t5_772jobs0 : List Job := [⟨plan4668,[],none,⟨10,6,0⟩⟩]

def t5_772jobs : List Job := t5_772jobs0




def t5_773root : Job := ⟨plan4669,[],none,⟨10,6,0⟩⟩
def t5_773jobs0 : List Job := [⟨plan4669,[],none,⟨10,6,0⟩⟩]

def t5_773jobs : List Job := t5_773jobs0




def t5_774root : Job := ⟨plan4670,[],none,⟨10,6,0⟩⟩
def t5_774jobs0 : List Job := [⟨plan4670,[],none,⟨10,6,0⟩⟩]

def t5_774jobs : List Job := t5_774jobs0




def t5_775root : Job := ⟨plan4671,[],none,⟨10,6,0⟩⟩
def t5_775jobs0 : List Job := [⟨plan4671,[],none,⟨10,6,0⟩⟩]

def t5_775jobs : List Job := t5_775jobs0




def t5_776root : Job := ⟨plan4289,[],none,⟨10,3,0⟩⟩
def t5_776jobs0 : List Job := [⟨plan4289,[],none,⟨10,3,0⟩⟩]

def t5_776jobs : List Job := t5_776jobs0




def t5_777root : Job := ⟨plan4672,[],none,⟨10,6,0⟩⟩
def t5_777jobs0 : List Job := [⟨plan4672,[],none,⟨10,6,0⟩⟩]

def t5_777jobs : List Job := t5_777jobs0




def t5_778root : Job := ⟨plan4673,[],none,⟨10,6,0⟩⟩
def t5_778jobs0 : List Job := [⟨plan4673,[],none,⟨10,6,0⟩⟩]

def t5_778jobs : List Job := t5_778jobs0




def t5_779root : Job := ⟨plan4674,[],none,⟨10,6,0⟩⟩
def t5_779jobs0 : List Job := [⟨plan4674,[],none,⟨10,6,0⟩⟩]

def t5_779jobs : List Job := t5_779jobs0




def t5_780root : Job := ⟨plan4675,[],none,⟨10,6,0⟩⟩
def t5_780jobs0 : List Job := [⟨plan4675,[],none,⟨10,6,0⟩⟩]

def t5_780jobs : List Job := t5_780jobs0




def t5_781root : Job := ⟨plan4676,[],none,⟨10,6,0⟩⟩
def t5_781jobs0 : List Job := [⟨plan4676,[],none,⟨10,6,0⟩⟩]

def t5_781jobs : List Job := t5_781jobs0




def t5_782root : Job := ⟨plan4677,[],none,⟨10,6,0⟩⟩
def t5_782jobs0 : List Job := [⟨plan4677,[],none,⟨10,6,0⟩⟩]

def t5_782jobs : List Job := t5_782jobs0




def t5_783root : Job := ⟨plan4678,[],none,⟨10,6,0⟩⟩
def t5_783jobs0 : List Job := [⟨plan4678,[],none,⟨10,6,0⟩⟩]

def t5_783jobs : List Job := t5_783jobs0




def t5_784root : Job := ⟨plan4679,[],none,⟨10,6,0⟩⟩
def t5_784jobs0 : List Job := [⟨plan2994,[⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨10,6,(-4)⟩⟩,⟨plan2994,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨9,6,(-3)⟩⟩]

def t5_784jobs1 : List Job := [⟨plan2994,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,6,(-2)⟩⟩]

def t5_784jobs : List Job := t5_784jobs0++t5_784jobs1




def t5_785root : Job := ⟨plan4680,[],none,⟨10,6,0⟩⟩
def t5_785jobs0 : List Job := [⟨plan4680,[],none,⟨10,6,0⟩⟩]

def t5_785jobs : List Job := t5_785jobs0




def t5_786root : Job := ⟨plan4681,[],none,⟨10,6,0⟩⟩
def t5_786jobs0 : List Job := [⟨plan2996,[⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨10,6,(-4)⟩⟩,⟨plan2996,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨9,6,(-3)⟩⟩]

def t5_786jobs1 : List Job := [⟨plan2996,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,6,(-2)⟩⟩]

def t5_786jobs : List Job := t5_786jobs0++t5_786jobs1




def t5_787root : Job := ⟨plan4682,[],none,⟨10,6,0⟩⟩
def t5_787jobs0 : List Job := [⟨plan1441,[⟨2,0,4⟩,⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨10,3,(-7)⟩⟩,⟨plan1441,[⟨2,0,4⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨9,4,(-5)⟩⟩,⟨plan1441,[⟨2,0,4⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨9,3,(-6)⟩⟩,⟨plan1441,[⟨2,0,4⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨8,5,(-3)⟩⟩,⟨plan1441,[⟨2,0,4⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨8,4,(-4)⟩⟩,⟨plan1441,[⟨2,1,3⟩,⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨9,3,(-6)⟩⟩,⟨plan1441,[⟨2,1,3⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨8,4,(-4)⟩⟩,⟨plan1441,[⟨2,1,3⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨8,3,(-5)⟩⟩,⟨plan1441,[⟨2,1,3⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨7,5,(-2)⟩⟩,⟨plan1441,[⟨2,1,3⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨7,4,(-3)⟩⟩,⟨plan1441,[⟨2,2,2⟩,⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨8,3,(-5)⟩⟩]

def t5_787jobs1 : List Job := [⟨plan1441,[⟨2,2,2⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨7,4,(-3)⟩⟩,⟨plan1441,[⟨2,2,2⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨7,3,(-4)⟩⟩,⟨plan1441,[⟨2,2,2⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨6,5,(-1)⟩⟩]

def t5_787jobs2 : List Job := [⟨plan1441,[⟨2,2,2⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨6,4,(-2)⟩⟩]

def t5_787jobs : List Job := t5_787jobs0++t5_787jobs1++t5_787jobs2



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


