-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks168
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks168
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:33:22.762215+00:00
-- url     : https://prove2.me/theorems/88a2cb90-bd2f-48e8-8d7b-df87677b73ed
-- title:
--   Endpoint22 Reach Checks168 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks168 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t7_240jobs0`, `ThreeBoundEndpoint22Reachable.t7_240jobs`, `ThreeBoundEndpoint22Reachable.t7_241root`, `ThreeBoundEndpoint22Reachable.t7_241jobs0`, `ThreeBoundEndpoint22Reachable.t7_241jobs`, `ThreeBoundEndpoint22Reachable.t7_231jobs2`, `ThreeBoundEndpoint22Reachable.t7_242root`, `ThreeBoundEndpoint22Reachable.t7_242jobs0`, `ThreeBoundEndpoint22Reachable.t7_242jobs`, `ThreeBoundEndpoint22Reachable.t7_243root`, `ThreeBoundEndpoint22Reachable.t7_243jobs0`, `ThreeBoundEndpoint22Reachable.t7_243jobs`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks168.lean, lines 1–218.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans088
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans089
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans091
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

def t7_231root : Job := ⟨plan8507,[],none,⟨21,6,0⟩⟩
def t7_231jobs0 : List Job := [⟨plan8143,[⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨21,6,(-4)⟩⟩,⟨plan8143,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨20,6,(-3)⟩⟩,⟨plan8143,[⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨20,6,(-4)⟩⟩,⟨plan8143,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨19,6,(-2)⟩⟩]

def t7_231jobs1 : List Job := [⟨plan8143,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨19,6,(-3)⟩⟩]

def t7_231jobs2 : List Job := [⟨plan8143,[⟨2,2,4⟩],(some ⟨2,2,4⟩),⟨19,6,(-4)⟩⟩]

def t7_231jobs : List Job := t7_231jobs0++t7_231jobs1++t7_231jobs2




def t7_232root : Job := ⟨plan8508,[],none,⟨21,6,0⟩⟩
def t7_232jobs0 : List Job := [⟨plan8144,[⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨21,6,(-4)⟩⟩,⟨plan8144,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨20,6,(-3)⟩⟩,⟨plan8144,[⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨20,6,(-4)⟩⟩,⟨plan8144,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨19,6,(-2)⟩⟩,⟨plan8144,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨19,6,(-3)⟩⟩]

def t7_232jobs1 : List Job := [⟨plan8144,[⟨2,2,4⟩],(some ⟨2,2,4⟩),⟨19,6,(-4)⟩⟩]

def t7_232jobs : List Job := t7_232jobs0++t7_232jobs1




def t7_233root : Job := ⟨plan8627,[],none,⟨21,10,0⟩⟩
def t7_233jobs0 : List Job := [⟨plan8627,[],none,⟨21,10,0⟩⟩]

def t7_233jobs : List Job := t7_233jobs0




def t7_234root : Job := ⟨plan8628,[],none,⟨21,10,0⟩⟩
def t7_234jobs0 : List Job := [⟨plan8216,[⟨2,0,5⟩],(some ⟨2,0,5⟩),⟨21,10,(-5)⟩⟩,⟨plan8216,[⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨20,10,(-4)⟩⟩,⟨plan8216,[⟨2,1,5⟩],(some ⟨2,1,5⟩),⟨20,10,(-5)⟩⟩]

def t7_234jobs1 : List Job := [⟨plan8216,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨19,10,(-3)⟩⟩]

def t7_234jobs2 : List Job := [⟨plan8216,[⟨2,2,4⟩],(some ⟨2,2,4⟩),⟨19,10,(-4)⟩⟩]

def t7_234jobs : List Job := t7_234jobs0++t7_234jobs1++t7_234jobs2




def t7_235root : Job := ⟨plan8629,[],none,⟨21,10,0⟩⟩
def t7_235jobs0 : List Job := [⟨plan8629,[],none,⟨21,10,0⟩⟩]

def t7_235jobs : List Job := t7_235jobs0




def t7_236root : Job := ⟨plan8630,[],none,⟨21,10,0⟩⟩
def t7_236jobs0 : List Job := [⟨plan8218,[⟨2,0,5⟩],(some ⟨2,0,5⟩),⟨21,10,(-5)⟩⟩,⟨plan8218,[⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨20,10,(-4)⟩⟩,⟨plan8218,[⟨2,1,5⟩],(some ⟨2,1,5⟩),⟨20,10,(-5)⟩⟩]

def t7_236jobs1 : List Job := [⟨plan8218,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨19,10,(-3)⟩⟩]

def t7_236jobs2 : List Job := [⟨plan8218,[⟨2,2,4⟩],(some ⟨2,2,4⟩),⟨19,10,(-4)⟩⟩]

def t7_236jobs : List Job := t7_236jobs0++t7_236jobs1++t7_236jobs2




def t7_237root : Job := ⟨plan8631,[],none,⟨21,10,0⟩⟩
def t7_237jobs0 : List Job := [⟨plan8219,[⟨2,0,5⟩],(some ⟨2,0,5⟩),⟨21,10,(-5)⟩⟩,⟨plan8219,[⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨20,10,(-4)⟩⟩,⟨plan8219,[⟨2,1,5⟩],(some ⟨2,1,5⟩),⟨20,10,(-5)⟩⟩]

def t7_237jobs1 : List Job := [⟨plan8219,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨19,10,(-3)⟩⟩]

def t7_237jobs2 : List Job := [⟨plan8219,[⟨2,2,4⟩],(some ⟨2,2,4⟩),⟨19,10,(-4)⟩⟩]

def t7_237jobs : List Job := t7_237jobs0++t7_237jobs1++t7_237jobs2




def t7_238root : Job := ⟨plan8632,[],none,⟨21,10,0⟩⟩
def t7_238jobs0 : List Job := [⟨plan8632,[],none,⟨21,10,0⟩⟩]

def t7_238jobs : List Job := t7_238jobs0




def t7_239root : Job := ⟨plan8794,[],none,⟨21,15,0⟩⟩
def t7_239jobs0 : List Job := [⟨plan8794,[],none,⟨21,15,0⟩⟩]

def t7_239jobs : List Job := t7_239jobs0




def t7_240root : Job := ⟨plan8795,[],none,⟨21,15,0⟩⟩
def t7_240jobs0 : List Job := [⟨plan8795,[],none,⟨21,15,0⟩⟩]

def t7_240jobs : List Job := t7_240jobs0




def t7_241root : Job := ⟨plan8796,[],none,⟨21,15,0⟩⟩
def t7_241jobs0 : List Job := [⟨plan8796,[],none,⟨21,15,0⟩⟩]

def t7_241jobs : List Job := t7_241jobs0




def t7_242root : Job := ⟨plan8797,[],none,⟨21,15,0⟩⟩
def t7_242jobs0 : List Job := [⟨plan8797,[],none,⟨21,15,0⟩⟩]

def t7_242jobs : List Job := t7_242jobs0




def t7_243root : Job := ⟨plan8798,[],none,⟨21,15,0⟩⟩
def t7_243jobs0 : List Job := [⟨plan8798,[],none,⟨21,15,0⟩⟩]

def t7_243jobs : List Job := t7_243jobs0




def t7_244root : Job := ⟨plan8799,[],none,⟨21,15,0⟩⟩
def t7_244jobs0 : List Job := [⟨plan8799,[],none,⟨21,15,0⟩⟩]

def t7_244jobs : List Job := t7_244jobs0




def t7_245root : Job := ⟨plan8800,[],none,⟨21,15,0⟩⟩
def t7_245jobs0 : List Job := [⟨plan8800,[],none,⟨21,15,0⟩⟩]

def t7_245jobs : List Job := t7_245jobs0




def t7_246root : Job := ⟨plan8633,[],none,⟨21,10,0⟩⟩
def t7_246jobs0 : List Job := [⟨plan8633,[],none,⟨21,10,0⟩⟩]

def t7_246jobs : List Job := t7_246jobs0




def t7_247root : Job := ⟨plan8801,[],none,⟨21,15,0⟩⟩
def t7_247jobs0 : List Job := [⟨plan8801,[],none,⟨21,15,0⟩⟩]

def t7_247jobs : List Job := t7_247jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


