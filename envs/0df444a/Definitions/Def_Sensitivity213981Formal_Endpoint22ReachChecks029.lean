-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks029
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks029
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:22:49.772981+00:00
-- url     : https://prove2.me/theorems/e7204cbd-3338-4f5a-aa2b-0377e34a1ca4
-- title:
--   Endpoint22 Reach Checks029 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks029 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t5_888root`, `ThreeBoundEndpoint22Reachable.t5_888jobs0`, `ThreeBoundEndpoint22Reachable.t5_888jobs`, `ThreeBoundEndpoint22Reachable.t5_889root`, `ThreeBoundEndpoint22Reachable.t5_889jobs0`, `ThreeBoundEndpoint22Reachable.t5_889jobs1`, `ThreeBoundEndpoint22Reachable.t5_889jobs2`, `ThreeBoundEndpoint22Reachable.t5_889jobs`, `ThreeBoundEndpoint22Reachable.t5_890root`, `ThreeBoundEndpoint22Reachable.t5_890jobs0`, `ThreeBoundEndpoint22Reachable.t5_890jobs1`, `ThreeBoundEndpoint22Reachable.t5_890jobs2`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks029.lean, lines 1–138.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
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

def t5_883root : Job := ⟨plan4738,[],none,⟨10,6,0⟩⟩
def t5_883jobs0 : List Job := [⟨plan3022,[⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨10,6,(-4)⟩⟩,⟨plan3022,[⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨9,6,(-3)⟩⟩,⟨plan3022,[⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨8,6,(-2)⟩⟩]

def t5_883jobs1 : List Job := [⟨plan3022,[⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨7,6,(-1)⟩⟩]

def t5_883jobs : List Job := t5_883jobs0++t5_883jobs1




def t5_884root : Job := ⟨plan4739,[],none,⟨10,6,0⟩⟩
def t5_884jobs0 : List Job := [⟨plan3023,[⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨10,6,(-4)⟩⟩,⟨plan3023,[⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨9,6,(-3)⟩⟩]

def t5_884jobs1 : List Job := [⟨plan3023,[⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨8,6,(-2)⟩⟩]

def t5_884jobs2 : List Job := [⟨plan3023,[⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨7,6,(-1)⟩⟩]

def t5_884jobs : List Job := t5_884jobs0++t5_884jobs1++t5_884jobs2




def t5_885root : Job := ⟨plan4740,[],none,⟨10,6,0⟩⟩
def t5_885jobs0 : List Job := [⟨plan1462,[⟨3,0,4⟩,⟨6,0,3⟩],(some ⟨6,0,3⟩),⟨10,3,(-7)⟩⟩,⟨plan1462,[⟨3,0,4⟩,⟨6,1,2⟩],(some ⟨6,1,2⟩),⟨9,4,(-5)⟩⟩,⟨plan1462,[⟨3,0,4⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨9,3,(-6)⟩⟩,⟨plan1462,[⟨3,0,4⟩,⟨6,2,1⟩],(some ⟨6,2,1⟩),⟨8,5,(-3)⟩⟩,⟨plan1462,[⟨3,0,4⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨8,4,(-4)⟩⟩,⟨plan1462,[⟨3,0,4⟩,⟨6,3,0⟩],(some ⟨6,3,0⟩),⟨7,6,(-1)⟩⟩,⟨plan1462,[⟨3,0,4⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨7,5,(-2)⟩⟩,⟨plan1462,[⟨3,1,3⟩,⟨6,0,3⟩],(some ⟨6,0,3⟩),⟨9,3,(-6)⟩⟩,⟨plan1462,[⟨3,1,3⟩,⟨6,1,2⟩],(some ⟨6,1,2⟩),⟨8,4,(-4)⟩⟩,⟨plan1462,[⟨3,1,3⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨8,3,(-5)⟩⟩,⟨plan1462,[⟨3,1,3⟩,⟨6,2,1⟩],(some ⟨6,2,1⟩),⟨7,5,(-2)⟩⟩,⟨plan1462,[⟨3,1,3⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨7,4,(-3)⟩⟩,⟨plan1462,[⟨3,1,3⟩,⟨6,3,0⟩],(some ⟨6,3,0⟩),⟨6,6,0⟩⟩,⟨plan1462,[⟨3,1,3⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨6,5,(-1)⟩⟩]

def t5_885jobs1 : List Job := [⟨plan1462,[⟨3,2,2⟩,⟨6,0,3⟩],(some ⟨6,0,3⟩),⟨8,3,(-5)⟩⟩,⟨plan1462,[⟨3,2,2⟩,⟨6,1,2⟩],(some ⟨6,1,2⟩),⟨7,4,(-3)⟩⟩,⟨plan1462,[⟨3,2,2⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨7,3,(-4)⟩⟩,⟨plan1462,[⟨3,2,2⟩,⟨6,2,1⟩],(some ⟨6,2,1⟩),⟨6,5,(-1)⟩⟩,⟨plan1462,[⟨3,2,2⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨6,4,(-2)⟩⟩]

def t5_885jobs2 : List Job := [⟨plan1462,[⟨3,2,2⟩,⟨6,3,0⟩],(some ⟨6,3,0⟩),⟨5,6,1⟩⟩,⟨plan1462,[⟨3,2,2⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨5,5,0⟩⟩,⟨plan1462,[⟨3,3,1⟩,⟨6,0,3⟩],(some ⟨6,0,3⟩),⟨7,3,(-4)⟩⟩,⟨plan1462,[⟨3,3,1⟩,⟨6,1,2⟩],(some ⟨6,1,2⟩),⟨6,4,(-2)⟩⟩,⟨plan1462,[⟨3,3,1⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨6,3,(-3)⟩⟩]

def t5_885jobs3 : List Job := [⟨plan1462,[⟨3,3,1⟩,⟨6,2,1⟩],(some ⟨6,2,1⟩),⟨5,5,0⟩⟩,⟨plan1462,[⟨3,3,1⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨5,4,(-1)⟩⟩,⟨plan1462,[⟨3,3,1⟩,⟨6,3,0⟩],(some ⟨6,3,0⟩),⟨4,6,2⟩⟩,⟨plan1462,[⟨3,3,1⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨4,5,1⟩⟩]

def t5_885jobs : List Job := t5_885jobs0++t5_885jobs1++t5_885jobs2++t5_885jobs3




def t5_886root : Job := ⟨plan4741,[],none,⟨10,6,0⟩⟩
def t5_886jobs0 : List Job := [⟨plan1463,[⟨3,0,4⟩,⟨6,0,3⟩],(some ⟨6,0,3⟩),⟨10,3,(-7)⟩⟩,⟨plan1463,[⟨3,0,4⟩,⟨6,1,2⟩],(some ⟨6,1,2⟩),⟨9,4,(-5)⟩⟩,⟨plan1463,[⟨3,0,4⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨9,3,(-6)⟩⟩,⟨plan1463,[⟨3,0,4⟩,⟨6,2,1⟩],(some ⟨6,2,1⟩),⟨8,5,(-3)⟩⟩,⟨plan1463,[⟨3,0,4⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨8,4,(-4)⟩⟩,⟨plan1463,[⟨3,0,4⟩,⟨6,3,0⟩],(some ⟨6,3,0⟩),⟨7,6,(-1)⟩⟩,⟨plan1463,[⟨3,0,4⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨7,5,(-2)⟩⟩,⟨plan1463,[⟨3,1,3⟩,⟨6,0,3⟩],(some ⟨6,0,3⟩),⟨9,3,(-6)⟩⟩,⟨plan1463,[⟨3,1,3⟩,⟨6,1,2⟩],(some ⟨6,1,2⟩),⟨8,4,(-4)⟩⟩,⟨plan1463,[⟨3,1,3⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨8,3,(-5)⟩⟩,⟨plan1463,[⟨3,1,3⟩,⟨6,2,1⟩],(some ⟨6,2,1⟩),⟨7,5,(-2)⟩⟩,⟨plan1463,[⟨3,1,3⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨7,4,(-3)⟩⟩,⟨plan1463,[⟨3,1,3⟩,⟨6,3,0⟩],(some ⟨6,3,0⟩),⟨6,6,0⟩⟩,⟨plan1463,[⟨3,1,3⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨6,5,(-1)⟩⟩,⟨plan1463,[⟨3,2,2⟩,⟨6,0,3⟩],(some ⟨6,0,3⟩),⟨8,3,(-5)⟩⟩,⟨plan1463,[⟨3,2,2⟩,⟨6,1,2⟩],(some ⟨6,1,2⟩),⟨7,4,(-3)⟩⟩]

def t5_886jobs1 : List Job := [⟨plan1463,[⟨3,2,2⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨7,3,(-4)⟩⟩,⟨plan1463,[⟨3,2,2⟩,⟨6,2,1⟩],(some ⟨6,2,1⟩),⟨6,5,(-1)⟩⟩,⟨plan1463,[⟨3,2,2⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨6,4,(-2)⟩⟩,⟨plan1463,[⟨3,2,2⟩,⟨6,3,0⟩],(some ⟨6,3,0⟩),⟨5,6,1⟩⟩,⟨plan1463,[⟨3,2,2⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨5,5,0⟩⟩,⟨plan1463,[⟨3,3,1⟩,⟨6,0,3⟩],(some ⟨6,0,3⟩),⟨7,3,(-4)⟩⟩]

def t5_886jobs2 : List Job := [⟨plan1463,[⟨3,3,1⟩,⟨6,1,2⟩],(some ⟨6,1,2⟩),⟨6,4,(-2)⟩⟩,⟨plan1463,[⟨3,3,1⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨6,3,(-3)⟩⟩,⟨plan1463,[⟨3,3,1⟩,⟨6,2,1⟩],(some ⟨6,2,1⟩),⟨5,5,0⟩⟩,⟨plan1463,[⟨3,3,1⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨5,4,(-1)⟩⟩,⟨plan1463,[⟨3,3,1⟩,⟨6,3,0⟩],(some ⟨6,3,0⟩),⟨4,6,2⟩⟩,⟨plan1463,[⟨3,3,1⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨4,5,1⟩⟩]

def t5_886jobs : List Job := t5_886jobs0++t5_886jobs1++t5_886jobs2




def t5_887root : Job := ⟨plan4742,[],none,⟨10,6,0⟩⟩
def t5_887jobs0 : List Job := [⟨plan3026,[⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨10,6,(-4)⟩⟩,⟨plan3026,[⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨9,6,(-3)⟩⟩,⟨plan3026,[⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨8,6,(-2)⟩⟩]

def t5_887jobs1 : List Job := [⟨plan3026,[⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨7,6,(-1)⟩⟩]

def t5_887jobs : List Job := t5_887jobs0++t5_887jobs1




def t5_888root : Job := ⟨plan4743,[],none,⟨10,6,0⟩⟩
def t5_888jobs0 : List Job := [⟨plan4743,[],none,⟨10,6,0⟩⟩]

def t5_888jobs : List Job := t5_888jobs0




def t5_889root : Job := ⟨plan4744,[],none,⟨10,6,0⟩⟩
def t5_889jobs0 : List Job := [⟨plan3107,[⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨10,6,(-4)⟩⟩,⟨plan3107,[⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨9,6,(-3)⟩⟩]

def t5_889jobs1 : List Job := [⟨plan3107,[⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨8,6,(-2)⟩⟩]

def t5_889jobs2 : List Job := [⟨plan3107,[⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨7,6,(-1)⟩⟩]

def t5_889jobs : List Job := t5_889jobs0++t5_889jobs1++t5_889jobs2




def t5_890root : Job := ⟨plan4745,[],none,⟨10,6,0⟩⟩
def t5_890jobs0 : List Job := [⟨plan3108,[⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨10,6,(-4)⟩⟩,⟨plan3108,[⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨9,6,(-3)⟩⟩]

def t5_890jobs1 : List Job := [⟨plan3108,[⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨8,6,(-2)⟩⟩]

def t5_890jobs2 : List Job := [⟨plan3108,[⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨7,6,(-1)⟩⟩]

def t5_890jobs : List Job := t5_890jobs0++t5_890jobs1++t5_890jobs2




def t5_891root : Job := ⟨plan4746,[],none,⟨10,6,0⟩⟩
def t5_891jobs0 : List Job := [⟨plan3109,[⟨3,0,4⟩],(some ⟨3,0,4⟩),⟨10,6,(-4)⟩⟩,⟨plan3109,[⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨9,6,(-3)⟩⟩,⟨plan3109,[⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨8,6,(-2)⟩⟩]

def t5_891jobs1 : List Job := [⟨plan3109,[⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨7,6,(-1)⟩⟩]

def t5_891jobs : List Job := t5_891jobs0++t5_891jobs1



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


