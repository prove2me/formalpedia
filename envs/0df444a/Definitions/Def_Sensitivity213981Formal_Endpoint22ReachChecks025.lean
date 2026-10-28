-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks025
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks025
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:25:45.675278+00:00
-- url     : https://prove2.me/theorems/26725b12-e224-46be-9d92-c3f572d4aa23
-- title:
--   Endpoint22 Reach Checks025 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks025 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t5_836root`, `ThreeBoundEndpoint22Reachable.t5_836jobs0`, `ThreeBoundEndpoint22Reachable.t5_836jobs`, `ThreeBoundEndpoint22Reachable.t5_837root`, `ThreeBoundEndpoint22Reachable.t5_837jobs0`, `ThreeBoundEndpoint22Reachable.t5_837jobs`, `ThreeBoundEndpoint22Reachable.t5_827jobs3`, `ThreeBoundEndpoint22Reachable.t5_838root`, `ThreeBoundEndpoint22Reachable.t5_838jobs0`, `ThreeBoundEndpoint22Reachable.t5_838jobs1`, `ThreeBoundEndpoint22Reachable.t5_838jobs`, `ThreeBoundEndpoint22Reachable.t5_827jobs`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks025.lean, lines 1–163.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans041
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans044
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans049
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

def t5_827root : Job := ⟨plan4298,[],none,⟨10,3,0⟩⟩
def t5_827jobs0 : List Job := [⟨plan2866,[⟨2,0,3⟩],(some ⟨2,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2866,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨9,3,(-2)⟩⟩]

def t5_827jobs1 : List Job := [⟨plan2866,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨9,3,(-3)⟩⟩]

def t5_827jobs2 : List Job := [⟨plan2866,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨8,3,(-1)⟩⟩]

def t5_827jobs3 : List Job := [⟨plan2866,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,3,(-2)⟩⟩]

def t5_827jobs : List Job := t5_827jobs0++t5_827jobs1++t5_827jobs2++t5_827jobs3




def t5_828root : Job := ⟨plan4299,[],none,⟨10,3,0⟩⟩
def t5_828jobs0 : List Job := [⟨plan2867,[⟨2,0,3⟩],(some ⟨2,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2867,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨9,3,(-2)⟩⟩,⟨plan2867,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨9,3,(-3)⟩⟩]

def t5_828jobs1 : List Job := [⟨plan2867,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨8,3,(-1)⟩⟩,⟨plan2867,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,3,(-2)⟩⟩]

def t5_828jobs : List Job := t5_828jobs0++t5_828jobs1




def t5_829root : Job := ⟨plan4709,[],none,⟨10,6,0⟩⟩
def t5_829jobs0 : List Job := [⟨plan4709,[],none,⟨10,6,0⟩⟩]

def t5_829jobs : List Job := t5_829jobs0




def t5_830root : Job := ⟨plan4710,[],none,⟨10,6,0⟩⟩
def t5_830jobs0 : List Job := [⟨plan3084,[⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨10,6,(-4)⟩⟩,⟨plan3084,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨9,6,(-3)⟩⟩]

def t5_830jobs1 : List Job := [⟨plan3084,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,6,(-2)⟩⟩]

def t5_830jobs : List Job := t5_830jobs0++t5_830jobs1




def t5_831root : Job := ⟨plan4711,[],none,⟨10,6,0⟩⟩
def t5_831jobs0 : List Job := [⟨plan4711,[],none,⟨10,6,0⟩⟩]

def t5_831jobs : List Job := t5_831jobs0




def t5_832root : Job := ⟨plan4712,[],none,⟨10,6,0⟩⟩
def t5_832jobs0 : List Job := [⟨plan3086,[⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨10,6,(-4)⟩⟩,⟨plan3086,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨9,6,(-3)⟩⟩]

def t5_832jobs1 : List Job := [⟨plan3086,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,6,(-2)⟩⟩]

def t5_832jobs : List Job := t5_832jobs0++t5_832jobs1




def t5_833root : Job := ⟨plan4713,[],none,⟨10,6,0⟩⟩
def t5_833jobs0 : List Job := [⟨plan1441,[⟨2,0,4⟩,⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨10,3,(-7)⟩⟩,⟨plan1441,[⟨2,0,4⟩,⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨9,4,(-5)⟩⟩,⟨plan1441,[⟨2,0,4⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨9,3,(-6)⟩⟩,⟨plan1441,[⟨2,0,4⟩,⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨8,5,(-3)⟩⟩,⟨plan1441,[⟨2,0,4⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨8,4,(-4)⟩⟩,⟨plan1441,[⟨2,1,3⟩,⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨9,3,(-6)⟩⟩,⟨plan1441,[⟨2,1,3⟩,⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨8,4,(-4)⟩⟩,⟨plan1441,[⟨2,1,3⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨8,3,(-5)⟩⟩,⟨plan1441,[⟨2,1,3⟩,⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨7,5,(-2)⟩⟩,⟨plan1441,[⟨2,1,3⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨7,4,(-3)⟩⟩,⟨plan1441,[⟨2,2,2⟩,⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨8,3,(-5)⟩⟩]

def t5_833jobs1 : List Job := [⟨plan1441,[⟨2,2,2⟩,⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨7,4,(-3)⟩⟩,⟨plan1441,[⟨2,2,2⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨7,3,(-4)⟩⟩,⟨plan1441,[⟨2,2,2⟩,⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨6,5,(-1)⟩⟩]

def t5_833jobs2 : List Job := [⟨plan1441,[⟨2,2,2⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨6,4,(-2)⟩⟩]

def t5_833jobs : List Job := t5_833jobs0++t5_833jobs1++t5_833jobs2




def t5_834root : Job := ⟨plan4714,[],none,⟨10,6,0⟩⟩
def t5_834jobs0 : List Job := [⟨plan4714,[],none,⟨10,6,0⟩⟩]

def t5_834jobs : List Job := t5_834jobs0




def t5_835root : Job := ⟨plan4715,[],none,⟨10,6,0⟩⟩
def t5_835jobs0 : List Job := [⟨plan4715,[],none,⟨10,6,0⟩⟩]

def t5_835jobs : List Job := t5_835jobs0




def t5_836root : Job := ⟨plan3942,[],none,⟨10,1,0⟩⟩
def t5_836jobs0 : List Job := [⟨plan3942,[],none,⟨10,1,0⟩⟩]

def t5_836jobs : List Job := t5_836jobs0




def t5_837root : Job := ⟨plan4300,[],none,⟨10,3,0⟩⟩
def t5_837jobs0 : List Job := [⟨plan4300,[],none,⟨10,3,0⟩⟩]

def t5_837jobs : List Job := t5_837jobs0




def t5_838root : Job := ⟨plan4301,[],none,⟨10,3,0⟩⟩
def t5_838jobs0 : List Job := [⟨plan2870,[⟨2,0,3⟩],(some ⟨2,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2870,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨9,3,(-2)⟩⟩,⟨plan2870,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨9,3,(-3)⟩⟩,⟨plan2870,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨8,3,(-1)⟩⟩]

def t5_838jobs1 : List Job := [⟨plan2870,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,3,(-2)⟩⟩]

def t5_838jobs : List Job := t5_838jobs0++t5_838jobs1



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


