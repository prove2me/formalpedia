-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks182
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks182
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:33:25.940982+00:00
-- url     : https://prove2.me/theorems/0edcc8fa-78d6-4eec-9f92-8e7e4c542601
-- title:
--   Endpoint22 Reach Checks182 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks182 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t7_331jobs1`, `ThreeBoundEndpoint22Reachable.t7_331jobs2`, `ThreeBoundEndpoint22Reachable.t7_331jobs3`, `ThreeBoundEndpoint22Reachable.t7_331jobs4`, `ThreeBoundEndpoint22Reachable.t7_331jobs`, `ThreeBoundEndpoint22Reachable.t7_328root`, `ThreeBoundEndpoint22Reachable.t7_332root`, `ThreeBoundEndpoint22Reachable.t7_332jobs0`, `ThreeBoundEndpoint22Reachable.t7_332jobs1`, `ThreeBoundEndpoint22Reachable.t7_328jobs0`, `ThreeBoundEndpoint22Reachable.t7_332jobs`, `ThreeBoundEndpoint22Reachable.t7_333root`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks182.lean, lines 1–139.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans091
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans092
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

def t7_327root : Job := ⟨plan8825,[],none,⟨21,15,0⟩⟩
def t7_327jobs0 : List Job := [⟨plan8825,[],none,⟨21,15,0⟩⟩]

def t7_327jobs : List Job := t7_327jobs0




def t7_328root : Job := ⟨plan8826,[],none,⟨21,15,0⟩⟩
def t7_328jobs0 : List Job := [⟨plan8826,[],none,⟨21,15,0⟩⟩]

def t7_328jobs : List Job := t7_328jobs0




def t7_329root : Job := ⟨plan8827,[],none,⟨21,15,0⟩⟩
def t7_329jobs0 : List Job := [⟨plan6225,[⟨3,0,6⟩,⟨6,0,5⟩],(some ⟨6,0,5⟩),⟨21,10,(-11)⟩⟩,⟨plan6225,[⟨3,0,6⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨20,11,(-9)⟩⟩,⟨plan6225,[⟨3,0,6⟩,⟨6,1,5⟩],(some ⟨6,1,5⟩),⟨20,10,(-10)⟩⟩,⟨plan6225,[⟨3,0,6⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨19,12,(-7)⟩⟩,⟨plan6225,[⟨3,0,6⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨19,11,(-8)⟩⟩,⟨plan6225,[⟨3,0,6⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨18,13,(-5)⟩⟩,⟨plan6225,[⟨3,0,6⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨18,12,(-6)⟩⟩,⟨plan6225,[⟨3,1,5⟩,⟨6,0,5⟩],(some ⟨6,0,5⟩),⟨20,10,(-10)⟩⟩,⟨plan6225,[⟨3,1,5⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨19,11,(-8)⟩⟩,⟨plan6225,[⟨3,1,5⟩,⟨6,1,5⟩],(some ⟨6,1,5⟩),⟨19,10,(-9)⟩⟩,⟨plan6225,[⟨3,1,5⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨18,12,(-6)⟩⟩,⟨plan6225,[⟨3,1,5⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨18,11,(-7)⟩⟩,⟨plan6225,[⟨3,1,5⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨17,13,(-4)⟩⟩,⟨plan6225,[⟨3,1,5⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨17,12,(-5)⟩⟩,⟨plan6225,[⟨3,2,4⟩,⟨6,0,5⟩],(some ⟨6,0,5⟩),⟨19,10,(-9)⟩⟩,⟨plan6225,[⟨3,2,4⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨18,11,(-7)⟩⟩,⟨plan6225,[⟨3,2,4⟩,⟨6,1,5⟩],(some ⟨6,1,5⟩),⟨18,10,(-8)⟩⟩,⟨plan6225,[⟨3,2,4⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨17,12,(-5)⟩⟩,⟨plan6225,[⟨3,2,4⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨17,11,(-6)⟩⟩]

def t7_329jobs1 : List Job := [⟨plan6225,[⟨3,2,4⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨16,13,(-3)⟩⟩,⟨plan6225,[⟨3,2,4⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨16,12,(-4)⟩⟩,⟨plan6225,[⟨3,3,3⟩,⟨6,0,5⟩],(some ⟨6,0,5⟩),⟨18,10,(-8)⟩⟩,⟨plan6225,[⟨3,3,3⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨17,11,(-6)⟩⟩,⟨plan6225,[⟨3,3,3⟩,⟨6,1,5⟩],(some ⟨6,1,5⟩),⟨17,10,(-7)⟩⟩]

def t7_329jobs2 : List Job := [⟨plan6225,[⟨3,3,3⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨16,12,(-4)⟩⟩,⟨plan6225,[⟨3,3,3⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨16,11,(-5)⟩⟩,⟨plan6225,[⟨3,3,3⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨15,13,(-2)⟩⟩]

def t7_329jobs3 : List Job := [⟨plan6225,[⟨3,3,3⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨15,12,(-3)⟩⟩]

def t7_329jobs : List Job := t7_329jobs0++t7_329jobs1++t7_329jobs2++t7_329jobs3




def t7_330root : Job := ⟨plan8828,[],none,⟨21,15,0⟩⟩
def t7_330jobs0 : List Job := [⟨plan6230,[⟨3,0,6⟩,⟨6,0,5⟩],(some ⟨6,0,5⟩),⟨21,10,(-11)⟩⟩,⟨plan6230,[⟨3,0,6⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨20,11,(-9)⟩⟩,⟨plan6230,[⟨3,0,6⟩,⟨6,1,5⟩],(some ⟨6,1,5⟩),⟨20,10,(-10)⟩⟩,⟨plan6230,[⟨3,0,6⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨19,12,(-7)⟩⟩,⟨plan6230,[⟨3,0,6⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨19,11,(-8)⟩⟩,⟨plan6230,[⟨3,0,6⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨18,13,(-5)⟩⟩,⟨plan6230,[⟨3,0,6⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨18,12,(-6)⟩⟩,⟨plan6230,[⟨3,1,5⟩,⟨6,0,5⟩],(some ⟨6,0,5⟩),⟨20,10,(-10)⟩⟩,⟨plan6230,[⟨3,1,5⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨19,11,(-8)⟩⟩,⟨plan6230,[⟨3,1,5⟩,⟨6,1,5⟩],(some ⟨6,1,5⟩),⟨19,10,(-9)⟩⟩,⟨plan6230,[⟨3,1,5⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨18,12,(-6)⟩⟩,⟨plan6230,[⟨3,1,5⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨18,11,(-7)⟩⟩,⟨plan6230,[⟨3,1,5⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨17,13,(-4)⟩⟩,⟨plan6230,[⟨3,1,5⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨17,12,(-5)⟩⟩,⟨plan6230,[⟨3,2,4⟩,⟨6,0,5⟩],(some ⟨6,0,5⟩),⟨19,10,(-9)⟩⟩,⟨plan6230,[⟨3,2,4⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨18,11,(-7)⟩⟩,⟨plan6230,[⟨3,2,4⟩,⟨6,1,5⟩],(some ⟨6,1,5⟩),⟨18,10,(-8)⟩⟩,⟨plan6230,[⟨3,2,4⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨17,12,(-5)⟩⟩]

def t7_330jobs1 : List Job := [⟨plan6230,[⟨3,2,4⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨17,11,(-6)⟩⟩,⟨plan6230,[⟨3,2,4⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨16,13,(-3)⟩⟩,⟨plan6230,[⟨3,2,4⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨16,12,(-4)⟩⟩]

def t7_330jobs2 : List Job := [⟨plan6230,[⟨3,3,3⟩,⟨6,0,5⟩],(some ⟨6,0,5⟩),⟨18,10,(-8)⟩⟩,⟨plan6230,[⟨3,3,3⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨17,11,(-6)⟩⟩,⟨plan6230,[⟨3,3,3⟩,⟨6,1,5⟩],(some ⟨6,1,5⟩),⟨17,10,(-7)⟩⟩]

def t7_330jobs3 : List Job := [⟨plan6230,[⟨3,3,3⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨16,12,(-4)⟩⟩,⟨plan6230,[⟨3,3,3⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨16,11,(-5)⟩⟩]

def t7_330jobs4 : List Job := [⟨plan6230,[⟨3,3,3⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨15,13,(-2)⟩⟩]

def t7_330jobs5 : List Job := [⟨plan6230,[⟨3,3,3⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨15,12,(-3)⟩⟩]

def t7_330jobs : List Job := t7_330jobs0++t7_330jobs1++t7_330jobs2++t7_330jobs3++t7_330jobs4++t7_330jobs5




def t7_331root : Job := ⟨plan8829,[],none,⟨21,15,0⟩⟩
def t7_331jobs0 : List Job := [⟨plan6231,[⟨3,0,6⟩,⟨6,0,5⟩],(some ⟨6,0,5⟩),⟨21,10,(-11)⟩⟩,⟨plan6231,[⟨3,0,6⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨20,11,(-9)⟩⟩,⟨plan6231,[⟨3,0,6⟩,⟨6,1,5⟩],(some ⟨6,1,5⟩),⟨20,10,(-10)⟩⟩,⟨plan6231,[⟨3,0,6⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨19,12,(-7)⟩⟩,⟨plan6231,[⟨3,0,6⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨19,11,(-8)⟩⟩,⟨plan6231,[⟨3,0,6⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨18,13,(-5)⟩⟩,⟨plan6231,[⟨3,0,6⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨18,12,(-6)⟩⟩,⟨plan6231,[⟨3,1,5⟩,⟨6,0,5⟩],(some ⟨6,0,5⟩),⟨20,10,(-10)⟩⟩,⟨plan6231,[⟨3,1,5⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨19,11,(-8)⟩⟩,⟨plan6231,[⟨3,1,5⟩,⟨6,1,5⟩],(some ⟨6,1,5⟩),⟨19,10,(-9)⟩⟩,⟨plan6231,[⟨3,1,5⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨18,12,(-6)⟩⟩,⟨plan6231,[⟨3,1,5⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨18,11,(-7)⟩⟩,⟨plan6231,[⟨3,1,5⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨17,13,(-4)⟩⟩,⟨plan6231,[⟨3,1,5⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨17,12,(-5)⟩⟩,⟨plan6231,[⟨3,2,4⟩,⟨6,0,5⟩],(some ⟨6,0,5⟩),⟨19,10,(-9)⟩⟩,⟨plan6231,[⟨3,2,4⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨18,11,(-7)⟩⟩,⟨plan6231,[⟨3,2,4⟩,⟨6,1,5⟩],(some ⟨6,1,5⟩),⟨18,10,(-8)⟩⟩,⟨plan6231,[⟨3,2,4⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨17,12,(-5)⟩⟩,⟨plan6231,[⟨3,2,4⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨17,11,(-6)⟩⟩,⟨plan6231,[⟨3,2,4⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨16,13,(-3)⟩⟩]

def t7_331jobs1 : List Job := [⟨plan6231,[⟨3,2,4⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨16,12,(-4)⟩⟩,⟨plan6231,[⟨3,3,3⟩,⟨6,0,5⟩],(some ⟨6,0,5⟩),⟨18,10,(-8)⟩⟩,⟨plan6231,[⟨3,3,3⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨17,11,(-6)⟩⟩,⟨plan6231,[⟨3,3,3⟩,⟨6,1,5⟩],(some ⟨6,1,5⟩),⟨17,10,(-7)⟩⟩]

def t7_331jobs2 : List Job := [⟨plan6231,[⟨3,3,3⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨16,12,(-4)⟩⟩,⟨plan6231,[⟨3,3,3⟩,⟨6,2,4⟩],(some ⟨6,2,4⟩),⟨16,11,(-5)⟩⟩]

def t7_331jobs3 : List Job := [⟨plan6231,[⟨3,3,3⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨15,13,(-2)⟩⟩]

def t7_331jobs4 : List Job := [⟨plan6231,[⟨3,3,3⟩,⟨6,3,3⟩],(some ⟨6,3,3⟩),⟨15,12,(-3)⟩⟩]

def t7_331jobs : List Job := t7_331jobs0++t7_331jobs1++t7_331jobs2++t7_331jobs3++t7_331jobs4




def t7_332root : Job := ⟨plan8830,[],none,⟨21,15,0⟩⟩
def t7_332jobs0 : List Job := [⟨plan8291,[⟨3,0,6⟩],(some ⟨3,0,6⟩),⟨21,15,(-6)⟩⟩,⟨plan8291,[⟨3,1,5⟩],(some ⟨3,1,5⟩),⟨20,15,(-5)⟩⟩,⟨plan8291,[⟨3,2,4⟩],(some ⟨3,2,4⟩),⟨19,15,(-4)⟩⟩]

def t7_332jobs1 : List Job := [⟨plan8291,[⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨18,15,(-3)⟩⟩]

def t7_332jobs : List Job := t7_332jobs0++t7_332jobs1




def t7_333root : Job := ⟨plan8831,[],none,⟨21,15,0⟩⟩
def t7_333jobs0 : List Job := [⟨plan8831,[],none,⟨21,15,0⟩⟩]

def t7_333jobs : List Job := t7_333jobs0




def t7_334root : Job := ⟨plan8832,[],none,⟨21,15,0⟩⟩
def t7_334jobs0 : List Job := [⟨plan8832,[],none,⟨21,15,0⟩⟩]

def t7_334jobs : List Job := t7_334jobs0




def t7_335root : Job := ⟨plan8833,[],none,⟨21,15,0⟩⟩
def t7_335jobs0 : List Job := [⟨plan8294,[⟨3,0,6⟩],(some ⟨3,0,6⟩),⟨21,15,(-6)⟩⟩,⟨plan8294,[⟨3,1,5⟩],(some ⟨3,1,5⟩),⟨20,15,(-5)⟩⟩,⟨plan8294,[⟨3,2,4⟩],(some ⟨3,2,4⟩),⟨19,15,(-4)⟩⟩]

def t7_335jobs1 : List Job := [⟨plan8294,[⟨3,3,3⟩],(some ⟨3,3,3⟩),⟨18,15,(-3)⟩⟩]

def t7_335jobs : List Job := t7_335jobs0++t7_335jobs1



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


