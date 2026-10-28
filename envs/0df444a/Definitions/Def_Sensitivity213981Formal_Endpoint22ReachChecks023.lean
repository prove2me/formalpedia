-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks023
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks023
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:24:01.076595+00:00
-- url     : https://prove2.me/theorems/56b8c669-709c-457d-b2be-4030c0f4ab1f
-- title:
--   Endpoint22 Reach Checks023 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks023 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t5_815jobs1`, `ThreeBoundEndpoint22Reachable.t5_815jobs2`, `ThreeBoundEndpoint22Reachable.t5_815jobs`, `ThreeBoundEndpoint22Reachable.t5_816root`, `ThreeBoundEndpoint22Reachable.t5_816jobs0`, `ThreeBoundEndpoint22Reachable.t5_816jobs1`, `ThreeBoundEndpoint22Reachable.t5_816jobs`, `ThreeBoundEndpoint22Reachable.t5_817root`, `ThreeBoundEndpoint22Reachable.t5_817jobs0`, `ThreeBoundEndpoint22Reachable.t5_817jobs`, `ThreeBoundEndpoint22Reachable.t5_818root`, `ThreeBoundEndpoint22Reachable.t5_818jobs0`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks023.lean, lines 1–194.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans039
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans048
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

def t5_805root : Job := ⟨plan4695,[],none,⟨10,6,0⟩⟩
def t5_805jobs0 : List Job := [⟨plan3014,[⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨10,6,(-4)⟩⟩,⟨plan3014,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨9,6,(-3)⟩⟩]

def t5_805jobs1 : List Job := [⟨plan3014,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,6,(-2)⟩⟩]

def t5_805jobs : List Job := t5_805jobs0++t5_805jobs1




def t5_806root : Job := ⟨plan4696,[],none,⟨10,6,0⟩⟩
def t5_806jobs0 : List Job := [⟨plan3015,[⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨10,6,(-4)⟩⟩,⟨plan3015,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨9,6,(-3)⟩⟩]

def t5_806jobs1 : List Job := [⟨plan3015,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,6,(-2)⟩⟩]

def t5_806jobs : List Job := t5_806jobs0++t5_806jobs1




def t5_807root : Job := ⟨plan4697,[],none,⟨10,6,0⟩⟩
def t5_807jobs0 : List Job := [⟨plan4697,[],none,⟨10,6,0⟩⟩]

def t5_807jobs : List Job := t5_807jobs0




def t5_808root : Job := ⟨plan4698,[],none,⟨10,6,0⟩⟩
def t5_808jobs0 : List Job := [⟨plan4698,[],none,⟨10,6,0⟩⟩]

def t5_808jobs : List Job := t5_808jobs0




def t5_809root : Job := ⟨plan4699,[],none,⟨10,6,0⟩⟩
def t5_809jobs0 : List Job := [⟨plan4699,[],none,⟨10,6,0⟩⟩]

def t5_809jobs : List Job := t5_809jobs0




def t5_810root : Job := ⟨plan4700,[],none,⟨10,6,0⟩⟩
def t5_810jobs0 : List Job := [⟨plan4700,[],none,⟨10,6,0⟩⟩]

def t5_810jobs : List Job := t5_810jobs0




def t5_811root : Job := ⟨plan4701,[],none,⟨10,6,0⟩⟩
def t5_811jobs0 : List Job := [⟨plan3020,[⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨10,6,(-4)⟩⟩,⟨plan3020,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨9,6,(-3)⟩⟩]

def t5_811jobs1 : List Job := [⟨plan3020,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,6,(-2)⟩⟩]

def t5_811jobs : List Job := t5_811jobs0++t5_811jobs1




def t5_812root : Job := ⟨plan4702,[],none,⟨10,6,0⟩⟩
def t5_812jobs0 : List Job := [⟨plan3021,[⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨10,6,(-4)⟩⟩,⟨plan3021,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨9,6,(-3)⟩⟩]

def t5_812jobs1 : List Job := [⟨plan3021,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,6,(-2)⟩⟩]

def t5_812jobs : List Job := t5_812jobs0++t5_812jobs1




def t5_813root : Job := ⟨plan4703,[],none,⟨10,6,0⟩⟩
def t5_813jobs0 : List Job := [⟨plan4703,[],none,⟨10,6,0⟩⟩]

def t5_813jobs : List Job := t5_813jobs0




def t5_814root : Job := ⟨plan4704,[],none,⟨10,6,0⟩⟩
def t5_814jobs0 : List Job := [⟨plan3023,[⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨10,6,(-4)⟩⟩,⟨plan3023,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨9,6,(-3)⟩⟩]

def t5_814jobs1 : List Job := [⟨plan3023,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,6,(-2)⟩⟩]

def t5_814jobs : List Job := t5_814jobs0++t5_814jobs1




def t5_815root : Job := ⟨plan4705,[],none,⟨10,6,0⟩⟩
def t5_815jobs0 : List Job := [⟨plan1462,[⟨2,0,4⟩,⟨6,0,3⟩],(some ⟨6,0,3⟩),⟨10,3,(-7)⟩⟩,⟨plan1462,[⟨2,0,4⟩,⟨6,1,2⟩],(some ⟨6,1,2⟩),⟨9,4,(-5)⟩⟩,⟨plan1462,[⟨2,0,4⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨9,3,(-6)⟩⟩,⟨plan1462,[⟨2,0,4⟩,⟨6,2,1⟩],(some ⟨6,2,1⟩),⟨8,5,(-3)⟩⟩,⟨plan1462,[⟨2,0,4⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨8,4,(-4)⟩⟩,⟨plan1462,[⟨2,0,4⟩,⟨6,3,0⟩],(some ⟨6,3,0⟩),⟨7,6,(-1)⟩⟩,⟨plan1462,[⟨2,0,4⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨7,5,(-2)⟩⟩,⟨plan1462,[⟨2,1,3⟩,⟨6,0,3⟩],(some ⟨6,0,3⟩),⟨9,3,(-6)⟩⟩,⟨plan1462,[⟨2,1,3⟩,⟨6,1,2⟩],(some ⟨6,1,2⟩),⟨8,4,(-4)⟩⟩,⟨plan1462,[⟨2,1,3⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨8,3,(-5)⟩⟩,⟨plan1462,[⟨2,1,3⟩,⟨6,2,1⟩],(some ⟨6,2,1⟩),⟨7,5,(-2)⟩⟩,⟨plan1462,[⟨2,1,3⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨7,4,(-3)⟩⟩,⟨plan1462,[⟨2,1,3⟩,⟨6,3,0⟩],(some ⟨6,3,0⟩),⟨6,6,0⟩⟩,⟨plan1462,[⟨2,1,3⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨6,5,(-1)⟩⟩]

def t5_815jobs1 : List Job := [⟨plan1462,[⟨2,2,2⟩,⟨6,0,3⟩],(some ⟨6,0,3⟩),⟨8,3,(-5)⟩⟩,⟨plan1462,[⟨2,2,2⟩,⟨6,1,2⟩],(some ⟨6,1,2⟩),⟨7,4,(-3)⟩⟩,⟨plan1462,[⟨2,2,2⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨7,3,(-4)⟩⟩,⟨plan1462,[⟨2,2,2⟩,⟨6,2,1⟩],(some ⟨6,2,1⟩),⟨6,5,(-1)⟩⟩,⟨plan1462,[⟨2,2,2⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨6,4,(-2)⟩⟩]

def t5_815jobs2 : List Job := [⟨plan1462,[⟨2,2,2⟩,⟨6,3,0⟩],(some ⟨6,3,0⟩),⟨5,6,1⟩⟩,⟨plan1462,[⟨2,2,2⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨5,5,0⟩⟩]

def t5_815jobs : List Job := t5_815jobs0++t5_815jobs1++t5_815jobs2




def t5_816root : Job := ⟨plan4706,[],none,⟨10,6,0⟩⟩
def t5_816jobs0 : List Job := [⟨plan1463,[⟨2,0,4⟩,⟨6,0,3⟩],(some ⟨6,0,3⟩),⟨10,3,(-7)⟩⟩,⟨plan1463,[⟨2,0,4⟩,⟨6,1,2⟩],(some ⟨6,1,2⟩),⟨9,4,(-5)⟩⟩,⟨plan1463,[⟨2,0,4⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨9,3,(-6)⟩⟩,⟨plan1463,[⟨2,0,4⟩,⟨6,2,1⟩],(some ⟨6,2,1⟩),⟨8,5,(-3)⟩⟩,⟨plan1463,[⟨2,0,4⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨8,4,(-4)⟩⟩,⟨plan1463,[⟨2,0,4⟩,⟨6,3,0⟩],(some ⟨6,3,0⟩),⟨7,6,(-1)⟩⟩,⟨plan1463,[⟨2,0,4⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨7,5,(-2)⟩⟩,⟨plan1463,[⟨2,1,3⟩,⟨6,0,3⟩],(some ⟨6,0,3⟩),⟨9,3,(-6)⟩⟩,⟨plan1463,[⟨2,1,3⟩,⟨6,1,2⟩],(some ⟨6,1,2⟩),⟨8,4,(-4)⟩⟩,⟨plan1463,[⟨2,1,3⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨8,3,(-5)⟩⟩,⟨plan1463,[⟨2,1,3⟩,⟨6,2,1⟩],(some ⟨6,2,1⟩),⟨7,5,(-2)⟩⟩,⟨plan1463,[⟨2,1,3⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨7,4,(-3)⟩⟩,⟨plan1463,[⟨2,1,3⟩,⟨6,3,0⟩],(some ⟨6,3,0⟩),⟨6,6,0⟩⟩,⟨plan1463,[⟨2,1,3⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨6,5,(-1)⟩⟩,⟨plan1463,[⟨2,2,2⟩,⟨6,0,3⟩],(some ⟨6,0,3⟩),⟨8,3,(-5)⟩⟩,⟨plan1463,[⟨2,2,2⟩,⟨6,1,2⟩],(some ⟨6,1,2⟩),⟨7,4,(-3)⟩⟩]

def t5_816jobs1 : List Job := [⟨plan1463,[⟨2,2,2⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨7,3,(-4)⟩⟩,⟨plan1463,[⟨2,2,2⟩,⟨6,2,1⟩],(some ⟨6,2,1⟩),⟨6,5,(-1)⟩⟩,⟨plan1463,[⟨2,2,2⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨6,4,(-2)⟩⟩,⟨plan1463,[⟨2,2,2⟩,⟨6,3,0⟩],(some ⟨6,3,0⟩),⟨5,6,1⟩⟩,⟨plan1463,[⟨2,2,2⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨5,5,0⟩⟩]

def t5_816jobs : List Job := t5_816jobs0++t5_816jobs1




def t5_817root : Job := ⟨plan4707,[],none,⟨10,6,0⟩⟩
def t5_817jobs0 : List Job := [⟨plan4707,[],none,⟨10,6,0⟩⟩]

def t5_817jobs : List Job := t5_817jobs0




def t5_818root : Job := ⟨plan4708,[],none,⟨10,6,0⟩⟩
def t5_818jobs0 : List Job := [⟨plan4708,[],none,⟨10,6,0⟩⟩]

def t5_818jobs : List Job := t5_818jobs0




def t5_819root : Job := ⟨plan3745,[],none,⟨10,0,0⟩⟩
def t5_819jobs0 : List Job := [⟨plan3745,[],none,⟨10,0,0⟩⟩]

def t5_819jobs : List Job := t5_819jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


