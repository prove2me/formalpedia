-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks024
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks024
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:26:29.258514+00:00
-- url     : https://prove2.me/theorems/c2bfb719-3f13-4a18-8d71-eda4a8e7fb70
-- title:
--   Endpoint22 Reach Checks024 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks024 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t5_820jobs`, `ThreeBoundEndpoint22Reachable.t5_821root`, `ThreeBoundEndpoint22Reachable.t5_821jobs0`, `ThreeBoundEndpoint22Reachable.t5_821jobs1`, `ThreeBoundEndpoint22Reachable.t5_821jobs2`, `ThreeBoundEndpoint22Reachable.t5_821jobs`, `ThreeBoundEndpoint22Reachable.t5_822root`, `ThreeBoundEndpoint22Reachable.t5_822jobs0`, `ThreeBoundEndpoint22Reachable.t5_822jobs1`, `ThreeBoundEndpoint22Reachable.t5_822jobs`, `ThreeBoundEndpoint22Reachable.t5_823root`, `ThreeBoundEndpoint22Reachable.t5_823jobs0`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks024.lean, lines 1–117.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans041
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

def t5_820root : Job := ⟨plan3939,[],none,⟨10,1,0⟩⟩
def t5_820jobs0 : List Job := [⟨plan2665,[⟨2,0,2⟩],(some ⟨2,0,2⟩),⟨10,1,(-2)⟩⟩,⟨plan2665,[⟨2,1,1⟩],(some ⟨2,1,1⟩),⟨9,1,(-1)⟩⟩,⟨plan2665,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨9,1,(-2)⟩⟩,⟨plan2665,[⟨2,2,0⟩],(some ⟨2,2,0⟩),⟨8,1,0⟩⟩]

def t5_820jobs1 : List Job := [⟨plan2665,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨8,1,(-1)⟩⟩,⟨plan2665,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,1,(-2)⟩⟩]

def t5_820jobs : List Job := t5_820jobs0++t5_820jobs1




def t5_821root : Job := ⟨plan3940,[],none,⟨10,1,0⟩⟩
def t5_821jobs0 : List Job := [⟨plan2666,[⟨2,0,2⟩],(some ⟨2,0,2⟩),⟨10,1,(-2)⟩⟩,⟨plan2666,[⟨2,1,1⟩],(some ⟨2,1,1⟩),⟨9,1,(-1)⟩⟩,⟨plan2666,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨9,1,(-2)⟩⟩]

def t5_821jobs1 : List Job := [⟨plan2666,[⟨2,2,0⟩],(some ⟨2,2,0⟩),⟨8,1,0⟩⟩,⟨plan2666,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨8,1,(-1)⟩⟩]

def t5_821jobs2 : List Job := [⟨plan2666,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,1,(-2)⟩⟩]

def t5_821jobs : List Job := t5_821jobs0++t5_821jobs1++t5_821jobs2




def t5_822root : Job := ⟨plan3941,[],none,⟨10,1,0⟩⟩
def t5_822jobs0 : List Job := [⟨plan2667,[⟨2,0,2⟩],(some ⟨2,0,2⟩),⟨10,1,(-2)⟩⟩,⟨plan2667,[⟨2,1,1⟩],(some ⟨2,1,1⟩),⟨9,1,(-1)⟩⟩,⟨plan2667,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨9,1,(-2)⟩⟩,⟨plan2667,[⟨2,2,0⟩],(some ⟨2,2,0⟩),⟨8,1,0⟩⟩]

def t5_822jobs1 : List Job := [⟨plan2667,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨8,1,(-1)⟩⟩,⟨plan2667,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,1,(-2)⟩⟩]

def t5_822jobs : List Job := t5_822jobs0++t5_822jobs1




def t5_823root : Job := ⟨plan4294,[],none,⟨10,3,0⟩⟩
def t5_823jobs0 : List Job := [⟨plan2862,[⟨2,0,3⟩],(some ⟨2,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2862,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨9,3,(-2)⟩⟩,⟨plan2862,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨9,3,(-3)⟩⟩]

def t5_823jobs1 : List Job := [⟨plan2862,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨8,3,(-1)⟩⟩,⟨plan2862,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,3,(-2)⟩⟩]

def t5_823jobs : List Job := t5_823jobs0++t5_823jobs1




def t5_824root : Job := ⟨plan4295,[],none,⟨10,3,0⟩⟩
def t5_824jobs0 : List Job := [⟨plan2863,[⟨2,0,3⟩],(some ⟨2,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2863,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨9,3,(-2)⟩⟩]

def t5_824jobs1 : List Job := [⟨plan2863,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨9,3,(-3)⟩⟩]

def t5_824jobs2 : List Job := [⟨plan2863,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨8,3,(-1)⟩⟩]

def t5_824jobs3 : List Job := [⟨plan2863,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,3,(-2)⟩⟩]

def t5_824jobs : List Job := t5_824jobs0++t5_824jobs1++t5_824jobs2++t5_824jobs3




def t5_825root : Job := ⟨plan4296,[],none,⟨10,3,0⟩⟩
def t5_825jobs0 : List Job := [⟨plan2864,[⟨2,0,3⟩],(some ⟨2,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2864,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨9,3,(-2)⟩⟩]

def t5_825jobs1 : List Job := [⟨plan2864,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨9,3,(-3)⟩⟩]

def t5_825jobs2 : List Job := [⟨plan2864,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨8,3,(-1)⟩⟩]

def t5_825jobs3 : List Job := [⟨plan2864,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,3,(-2)⟩⟩]

def t5_825jobs : List Job := t5_825jobs0++t5_825jobs1++t5_825jobs2++t5_825jobs3




def t5_826root : Job := ⟨plan4297,[],none,⟨10,3,0⟩⟩
def t5_826jobs0 : List Job := [⟨plan2865,[⟨2,0,3⟩],(some ⟨2,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2865,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨9,3,(-2)⟩⟩]

def t5_826jobs1 : List Job := [⟨plan2865,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨9,3,(-3)⟩⟩]

def t5_826jobs2 : List Job := [⟨plan2865,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨8,3,(-1)⟩⟩]

def t5_826jobs3 : List Job := [⟨plan2865,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,3,(-2)⟩⟩]

def t5_826jobs : List Job := t5_826jobs0++t5_826jobs1++t5_826jobs2++t5_826jobs3



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


