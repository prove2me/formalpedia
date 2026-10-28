-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks036
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks036
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:25:31.752621+00:00
-- url     : https://prove2.me/theorems/dab046d2-8ba6-488d-a7b8-4741236a142d
-- title:
--   Endpoint22 Reach Checks036 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks036 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t5_1230root`, `ThreeBoundEndpoint22Reachable.t5_1230jobs0`, `ThreeBoundEndpoint22Reachable.t5_1230jobs1`, `ThreeBoundEndpoint22Reachable.t5_1230jobs`, `ThreeBoundEndpoint22Reachable.t5_1223root`, `ThreeBoundEndpoint22Reachable.t5_1223jobs0`, `ThreeBoundEndpoint22Reachable.t5_1223jobs1`, `ThreeBoundEndpoint22Reachable.t5_1223jobs`, `ThreeBoundEndpoint22Reachable.t5_1224root`, `ThreeBoundEndpoint22Reachable.t5_1224jobs0`, `ThreeBoundEndpoint22Reachable.t5_1224jobs1`, `ThreeBoundEndpoint22Reachable.t5_1224jobs`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks036.lean, lines 1–136.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans050
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

def t5_1222root : Job := ⟨plan4857,[],none,⟨10,6,0⟩⟩
def t5_1222jobs0 : List Job := [⟨plan4857,[],none,⟨10,6,0⟩⟩]

def t5_1222jobs : List Job := t5_1222jobs0




def t5_1223root : Job := ⟨plan4858,[],none,⟨10,6,0⟩⟩
def t5_1223jobs0 : List Job := [⟨plan2905,[⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2905,[⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨9,4,(-1)⟩⟩,⟨plan2905,[⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨9,3,(-2)⟩⟩]

def t5_1223jobs1 : List Job := [⟨plan2905,[⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨8,5,1⟩⟩,⟨plan2905,[⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨8,4,0⟩⟩]

def t5_1223jobs : List Job := t5_1223jobs0++t5_1223jobs1




def t5_1224root : Job := ⟨plan4859,[],none,⟨10,6,0⟩⟩
def t5_1224jobs0 : List Job := [⟨plan2906,[⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2906,[⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨9,4,(-1)⟩⟩,⟨plan2906,[⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨9,3,(-2)⟩⟩,⟨plan2906,[⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨8,5,1⟩⟩]

def t5_1224jobs1 : List Job := [⟨plan2906,[⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨8,4,0⟩⟩]

def t5_1224jobs : List Job := t5_1224jobs0++t5_1224jobs1




def t5_1225root : Job := ⟨plan4860,[],none,⟨10,6,0⟩⟩
def t5_1225jobs0 : List Job := [⟨plan2907,[⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2907,[⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨9,4,(-1)⟩⟩]

def t5_1225jobs1 : List Job := [⟨plan2907,[⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨9,3,(-2)⟩⟩,⟨plan2907,[⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨8,5,1⟩⟩]

def t5_1225jobs2 : List Job := [⟨plan2907,[⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨8,4,0⟩⟩]

def t5_1225jobs : List Job := t5_1225jobs0++t5_1225jobs1++t5_1225jobs2




def t5_1226root : Job := ⟨plan4861,[],none,⟨10,6,0⟩⟩
def t5_1226jobs0 : List Job := [⟨plan2908,[⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨10,3,(-3)⟩⟩]

def t5_1226jobs1 : List Job := [⟨plan2908,[⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨9,4,(-1)⟩⟩]

def t5_1226jobs2 : List Job := [⟨plan2908,[⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨9,3,(-2)⟩⟩]

def t5_1226jobs3 : List Job := [⟨plan2908,[⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨8,5,1⟩⟩]

def t5_1226jobs4 : List Job := [⟨plan2908,[⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨8,4,0⟩⟩]

def t5_1226jobs : List Job := t5_1226jobs0++t5_1226jobs1++t5_1226jobs2++t5_1226jobs3++t5_1226jobs4




def t5_1227root : Job := ⟨plan4862,[],none,⟨10,6,0⟩⟩
def t5_1227jobs0 : List Job := [⟨plan2909,[⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2909,[⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨9,4,(-1)⟩⟩,⟨plan2909,[⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨9,3,(-2)⟩⟩]

def t5_1227jobs1 : List Job := [⟨plan2909,[⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨8,5,1⟩⟩,⟨plan2909,[⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨8,4,0⟩⟩]

def t5_1227jobs : List Job := t5_1227jobs0++t5_1227jobs1




def t5_1228root : Job := ⟨plan4863,[],none,⟨10,6,0⟩⟩
def t5_1228jobs0 : List Job := [⟨plan2910,[⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2910,[⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨9,4,(-1)⟩⟩,⟨plan2910,[⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨9,3,(-2)⟩⟩,⟨plan2910,[⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨8,5,1⟩⟩]

def t5_1228jobs1 : List Job := [⟨plan2910,[⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨8,4,0⟩⟩]

def t5_1228jobs : List Job := t5_1228jobs0++t5_1228jobs1




def t5_1229root : Job := ⟨plan4864,[],none,⟨10,6,0⟩⟩
def t5_1229jobs0 : List Job := [⟨plan2911,[⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2911,[⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨9,4,(-1)⟩⟩]

def t5_1229jobs1 : List Job := [⟨plan2911,[⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨9,3,(-2)⟩⟩,⟨plan2911,[⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨8,5,1⟩⟩]

def t5_1229jobs2 : List Job := [⟨plan2911,[⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨8,4,0⟩⟩]

def t5_1229jobs : List Job := t5_1229jobs0++t5_1229jobs1++t5_1229jobs2




def t5_1230root : Job := ⟨plan4865,[],none,⟨10,6,0⟩⟩
def t5_1230jobs0 : List Job := [⟨plan2912,[⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2912,[⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨9,4,(-1)⟩⟩,⟨plan2912,[⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨9,3,(-2)⟩⟩]

def t5_1230jobs1 : List Job := [⟨plan2912,[⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨8,5,1⟩⟩,⟨plan2912,[⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨8,4,0⟩⟩]

def t5_1230jobs : List Job := t5_1230jobs0++t5_1230jobs1



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


