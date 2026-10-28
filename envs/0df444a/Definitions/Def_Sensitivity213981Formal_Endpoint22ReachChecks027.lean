-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks027
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks027
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:27:13.344806+00:00
-- url     : https://prove2.me/theorems/7c8723e2-e370-46ea-a524-f5ac3f465731
-- title:
--   Endpoint22 Reach Checks027 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks027 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t5_865jobs1`, `ThreeBoundEndpoint22Reachable.t5_865jobs`, `ThreeBoundEndpoint22Reachable.t5_866root`, `ThreeBoundEndpoint22Reachable.t5_866jobs0`, `ThreeBoundEndpoint22Reachable.t5_866jobs1`, `ThreeBoundEndpoint22Reachable.t5_866jobs`, `ThreeBoundEndpoint22Reachable.t5_867root`, `ThreeBoundEndpoint22Reachable.t5_867jobs0`, `ThreeBoundEndpoint22Reachable.t5_867jobs`, `ThreeBoundEndpoint22Reachable.t5_868root`, `ThreeBoundEndpoint22Reachable.t5_868jobs0`, `ThreeBoundEndpoint22Reachable.t5_868jobs`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks027.lean, lines 1–124.

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

def t5_865root : Job := ⟨plan3946,[],none,⟨10,1,0⟩⟩
def t5_865jobs0 : List Job := [⟨plan2633,[⟨3,0,2⟩],(some ⟨3,0,2⟩),⟨10,1,(-2)⟩⟩,⟨plan2633,[⟨3,1,1⟩],(some ⟨3,1,1⟩),⟨9,1,(-1)⟩⟩,⟨plan2633,[⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨9,1,(-2)⟩⟩,⟨plan2633,[⟨3,2,0⟩],(some ⟨3,2,0⟩),⟨8,1,0⟩⟩,⟨plan2633,[⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨8,1,(-1)⟩⟩,⟨plan2633,[⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨8,1,(-2)⟩⟩]

def t5_865jobs1 : List Job := [⟨plan2633,[⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨7,1,0⟩⟩,⟨plan2633,[⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨7,1,(-1)⟩⟩]

def t5_865jobs : List Job := t5_865jobs0++t5_865jobs1




def t5_866root : Job := ⟨plan3947,[],none,⟨10,1,0⟩⟩
def t5_866jobs0 : List Job := [⟨plan2634,[⟨3,0,2⟩],(some ⟨3,0,2⟩),⟨10,1,(-2)⟩⟩,⟨plan2634,[⟨3,1,1⟩],(some ⟨3,1,1⟩),⟨9,1,(-1)⟩⟩,⟨plan2634,[⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨9,1,(-2)⟩⟩]

def t5_866jobs1 : List Job := [⟨plan2634,[⟨3,2,0⟩],(some ⟨3,2,0⟩),⟨8,1,0⟩⟩,⟨plan2634,[⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨8,1,(-1)⟩⟩,⟨plan2634,[⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨8,1,(-2)⟩⟩,⟨plan2634,[⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨7,1,0⟩⟩,⟨plan2634,[⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨7,1,(-1)⟩⟩]

def t5_866jobs : List Job := t5_866jobs0++t5_866jobs1




def t5_867root : Job := ⟨plan3948,[],none,⟨10,1,0⟩⟩
def t5_867jobs0 : List Job := [⟨plan3948,[],none,⟨10,1,0⟩⟩]

def t5_867jobs : List Job := t5_867jobs0




def t5_868root : Job := ⟨plan4304,[],none,⟨10,3,0⟩⟩
def t5_868jobs0 : List Job := [⟨plan4304,[],none,⟨10,3,0⟩⟩]

def t5_868jobs : List Job := t5_868jobs0




def t5_869root : Job := ⟨plan4305,[],none,⟨10,3,0⟩⟩
def t5_869jobs0 : List Job := [⟨plan2769,[⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2769,[⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨9,3,(-2)⟩⟩]

def t5_869jobs1 : List Job := [⟨plan2769,[⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨9,3,(-3)⟩⟩,⟨plan2769,[⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨8,3,(-1)⟩⟩]

def t5_869jobs2 : List Job := [⟨plan2769,[⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨8,3,(-2)⟩⟩,⟨plan2769,[⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨7,3,0⟩⟩,⟨plan2769,[⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨7,3,(-1)⟩⟩]

def t5_869jobs : List Job := t5_869jobs0++t5_869jobs1++t5_869jobs2




def t5_870root : Job := ⟨plan4306,[],none,⟨10,3,0⟩⟩
def t5_870jobs0 : List Job := [⟨plan2770,[⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2770,[⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨9,3,(-2)⟩⟩,⟨plan2770,[⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨9,3,(-3)⟩⟩]

def t5_870jobs1 : List Job := [⟨plan2770,[⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨8,3,(-1)⟩⟩,⟨plan2770,[⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨8,3,(-2)⟩⟩,⟨plan2770,[⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨7,3,0⟩⟩,⟨plan2770,[⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨7,3,(-1)⟩⟩]

def t5_870jobs : List Job := t5_870jobs0++t5_870jobs1




def t5_871root : Job := ⟨plan4307,[],none,⟨10,3,0⟩⟩
def t5_871jobs0 : List Job := [⟨plan2771,[⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2771,[⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨9,3,(-2)⟩⟩]

def t5_871jobs1 : List Job := [⟨plan2771,[⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨9,3,(-3)⟩⟩]

def t5_871jobs2 : List Job := [⟨plan2771,[⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨8,3,(-1)⟩⟩,⟨plan2771,[⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨8,3,(-2)⟩⟩]

def t5_871jobs3 : List Job := [⟨plan2771,[⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨7,3,0⟩⟩,⟨plan2771,[⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨7,3,(-1)⟩⟩]

def t5_871jobs : List Job := t5_871jobs0++t5_871jobs1++t5_871jobs2++t5_871jobs3




def t5_872root : Job := ⟨plan4308,[],none,⟨10,3,0⟩⟩
def t5_872jobs0 : List Job := [⟨plan2772,[⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨10,3,(-3)⟩⟩]

def t5_872jobs1 : List Job := [⟨plan2772,[⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨9,3,(-2)⟩⟩]

def t5_872jobs2 : List Job := [⟨plan2772,[⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨9,3,(-3)⟩⟩]

def t5_872jobs3 : List Job := [⟨plan2772,[⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨8,3,(-1)⟩⟩]

def t5_872jobs4 : List Job := [⟨plan2772,[⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨8,3,(-2)⟩⟩,⟨plan2772,[⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨7,3,0⟩⟩,⟨plan2772,[⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨7,3,(-1)⟩⟩]

def t5_872jobs : List Job := t5_872jobs0++t5_872jobs1++t5_872jobs2++t5_872jobs3++t5_872jobs4



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


