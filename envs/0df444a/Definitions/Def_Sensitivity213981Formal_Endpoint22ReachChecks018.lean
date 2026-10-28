-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks018
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks018
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:22:30.618573+00:00
-- url     : https://prove2.me/theorems/adaf0870-2523-49d1-87e9-e74532ae5012
-- title:
--   Endpoint22 Reach Checks018 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks018 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t5_742jobs`, `ThreeBoundEndpoint22Reachable.t5_743root`, `ThreeBoundEndpoint22Reachable.t5_743jobs0`, `ThreeBoundEndpoint22Reachable.t5_743jobs1`, `ThreeBoundEndpoint22Reachable.t5_743jobs2`, `ThreeBoundEndpoint22Reachable.t5_743jobs3`, `ThreeBoundEndpoint22Reachable.t5_743jobs`, `ThreeBoundEndpoint22Reachable.t5_744root`, `ThreeBoundEndpoint22Reachable.t5_744jobs0`, `ThreeBoundEndpoint22Reachable.t5_744jobs1`, `ThreeBoundEndpoint22Reachable.t5_744jobs2`, `ThreeBoundEndpoint22Reachable.t5_744jobs`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks018.lean, lines 1–94.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
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

def t5_742root : Job := ⟨plan4269,[],none,⟨10,3,0⟩⟩
def t5_742jobs0 : List Job := [⟨plan2768,[⟨2,0,3⟩],(some ⟨2,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2768,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨9,3,(-2)⟩⟩,⟨plan2768,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨9,3,(-3)⟩⟩,⟨plan2768,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨8,3,(-1)⟩⟩]

def t5_742jobs1 : List Job := [⟨plan2768,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,3,(-2)⟩⟩]

def t5_742jobs : List Job := t5_742jobs0++t5_742jobs1




def t5_743root : Job := ⟨plan4270,[],none,⟨10,3,0⟩⟩
def t5_743jobs0 : List Job := [⟨plan2769,[⟨2,0,3⟩],(some ⟨2,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2769,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨9,3,(-2)⟩⟩]

def t5_743jobs1 : List Job := [⟨plan2769,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨9,3,(-3)⟩⟩]

def t5_743jobs2 : List Job := [⟨plan2769,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨8,3,(-1)⟩⟩]

def t5_743jobs3 : List Job := [⟨plan2769,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,3,(-2)⟩⟩]

def t5_743jobs : List Job := t5_743jobs0++t5_743jobs1++t5_743jobs2++t5_743jobs3




def t5_744root : Job := ⟨plan4271,[],none,⟨10,3,0⟩⟩
def t5_744jobs0 : List Job := [⟨plan2770,[⟨2,0,3⟩],(some ⟨2,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2770,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨9,3,(-2)⟩⟩]

def t5_744jobs1 : List Job := [⟨plan2770,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨9,3,(-3)⟩⟩,⟨plan2770,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨8,3,(-1)⟩⟩]

def t5_744jobs2 : List Job := [⟨plan2770,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,3,(-2)⟩⟩]

def t5_744jobs : List Job := t5_744jobs0++t5_744jobs1++t5_744jobs2




def t5_745root : Job := ⟨plan4272,[],none,⟨10,3,0⟩⟩
def t5_745jobs0 : List Job := [⟨plan2771,[⟨2,0,3⟩],(some ⟨2,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2771,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨9,3,(-2)⟩⟩]

def t5_745jobs1 : List Job := [⟨plan2771,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨9,3,(-3)⟩⟩]

def t5_745jobs2 : List Job := [⟨plan2771,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨8,3,(-1)⟩⟩]

def t5_745jobs3 : List Job := [⟨plan2771,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,3,(-2)⟩⟩]

def t5_745jobs : List Job := t5_745jobs0++t5_745jobs1++t5_745jobs2++t5_745jobs3




def t5_746root : Job := ⟨plan4273,[],none,⟨10,3,0⟩⟩
def t5_746jobs0 : List Job := [⟨plan1374,[⟨2,0,3⟩,⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨10,3,(-6)⟩⟩,⟨plan1374,[⟨2,0,3⟩,⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨9,3,(-5)⟩⟩,⟨plan1374,[⟨2,0,3⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨9,3,(-6)⟩⟩,⟨plan1374,[⟨2,0,3⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨8,3,(-4)⟩⟩,⟨plan1374,[⟨2,0,3⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨8,3,(-5)⟩⟩,⟨plan1374,[⟨2,0,3⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨7,3,(-3)⟩⟩,⟨plan1374,[⟨2,0,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨7,3,(-4)⟩⟩,⟨plan1374,[⟨2,1,2⟩,⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨9,3,(-5)⟩⟩,⟨plan1374,[⟨2,1,2⟩,⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨8,3,(-4)⟩⟩,⟨plan1374,[⟨2,1,2⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨8,3,(-5)⟩⟩,⟨plan1374,[⟨2,1,2⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨7,3,(-3)⟩⟩]

def t5_746jobs1 : List Job := [⟨plan1374,[⟨2,1,2⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨7,3,(-4)⟩⟩,⟨plan1374,[⟨2,1,2⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨6,3,(-2)⟩⟩,⟨plan1374,[⟨2,1,2⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨6,3,(-3)⟩⟩,⟨plan1374,[⟨2,1,3⟩,⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨9,3,(-6)⟩⟩]

def t5_746jobs2 : List Job := [⟨plan1374,[⟨2,1,3⟩,⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨8,3,(-5)⟩⟩,⟨plan1374,[⟨2,1,3⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨8,3,(-6)⟩⟩,⟨plan1374,[⟨2,1,3⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨7,3,(-4)⟩⟩,⟨plan1374,[⟨2,1,3⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨7,3,(-5)⟩⟩,⟨plan1374,[⟨2,1,3⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨6,3,(-3)⟩⟩,⟨plan1374,[⟨2,1,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨6,3,(-4)⟩⟩,⟨plan1374,[⟨2,2,1⟩,⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨8,3,(-4)⟩⟩,⟨plan1374,[⟨2,2,1⟩,⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨7,3,(-3)⟩⟩]

def t5_746jobs3 : List Job := [⟨plan1374,[⟨2,2,1⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨7,3,(-4)⟩⟩,⟨plan1374,[⟨2,2,1⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨6,3,(-2)⟩⟩,⟨plan1374,[⟨2,2,1⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨6,3,(-3)⟩⟩,⟨plan1374,[⟨2,2,1⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨5,3,(-1)⟩⟩]

def t5_746jobs4 : List Job := [⟨plan1374,[⟨2,2,1⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨5,3,(-2)⟩⟩,⟨plan1374,[⟨2,2,2⟩,⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨8,3,(-5)⟩⟩,⟨plan1374,[⟨2,2,2⟩,⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨7,3,(-4)⟩⟩,⟨plan1374,[⟨2,2,2⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨7,3,(-5)⟩⟩]

def t5_746jobs5 : List Job := [⟨plan1374,[⟨2,2,2⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨6,3,(-3)⟩⟩,⟨plan1374,[⟨2,2,2⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨6,3,(-4)⟩⟩,⟨plan1374,[⟨2,2,2⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨5,3,(-2)⟩⟩,⟨plan1374,[⟨2,2,2⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨5,3,(-3)⟩⟩]

def t5_746jobs : List Job := t5_746jobs0++t5_746jobs1++t5_746jobs2++t5_746jobs3++t5_746jobs4++t5_746jobs5



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


