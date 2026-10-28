-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks038
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks038
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:27:27.754254+00:00
-- url     : https://prove2.me/theorems/46490dee-e5d7-41d7-8c5e-39737d2fead4
-- title:
--   Endpoint22 Reach Checks038 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks038 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t5_1301jobs`, `ThreeBoundEndpoint22Reachable.t5_1302root`, `ThreeBoundEndpoint22Reachable.t5_1302jobs0`, `ThreeBoundEndpoint22Reachable.t5_1302jobs1`, `ThreeBoundEndpoint22Reachable.t5_1302jobs`, `ThreeBoundEndpoint22Reachable.t5_1303root`, `ThreeBoundEndpoint22Reachable.t5_1303jobs0`, `ThreeBoundEndpoint22Reachable.t5_1303jobs`, `ThreeBoundEndpoint22Reachable.t5_1304root`, `ThreeBoundEndpoint22Reachable.t5_1304jobs0`, `ThreeBoundEndpoint22Reachable.t5_1291root`, `ThreeBoundEndpoint22Reachable.t5_1304jobs1`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks038.lean, lines 1–217.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans041
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans045
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans050
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans053
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

def t5_1290root : Job := ⟨plan5160,[],none,⟨10,10,0⟩⟩
def t5_1290jobs0 : List Job := [⟨plan5160,[],none,⟨10,10,0⟩⟩]

def t5_1290jobs : List Job := t5_1290jobs0




def t5_1291root : Job := ⟨plan5161,[],none,⟨10,10,0⟩⟩
def t5_1291jobs0 : List Job := [⟨plan5161,[],none,⟨10,10,0⟩⟩]

def t5_1291jobs : List Job := t5_1291jobs0




def t5_1292root : Job := ⟨plan5162,[],none,⟨10,10,0⟩⟩
def t5_1292jobs0 : List Job := [⟨plan5162,[],none,⟨10,10,0⟩⟩]

def t5_1292jobs : List Job := t5_1292jobs0




def t5_1293root : Job := ⟨plan5163,[],none,⟨10,10,0⟩⟩
def t5_1293jobs0 : List Job := [⟨plan5163,[],none,⟨10,10,0⟩⟩]

def t5_1293jobs : List Job := t5_1293jobs0




def t5_1294root : Job := ⟨plan5164,[],none,⟨10,10,0⟩⟩
def t5_1294jobs0 : List Job := [⟨plan5164,[],none,⟨10,10,0⟩⟩]

def t5_1294jobs : List Job := t5_1294jobs0




def t5_1295root : Job := ⟨plan5165,[],none,⟨10,10,0⟩⟩
def t5_1295jobs0 : List Job := [⟨plan5165,[],none,⟨10,10,0⟩⟩]

def t5_1295jobs : List Job := t5_1295jobs0




def t5_1296root : Job := ⟨plan5166,[],none,⟨10,10,0⟩⟩
def t5_1296jobs0 : List Job := [⟨plan5166,[],none,⟨10,10,0⟩⟩]

def t5_1296jobs : List Job := t5_1296jobs0




def t5_1297root : Job := ⟨plan5167,[],none,⟨10,10,0⟩⟩
def t5_1297jobs0 : List Job := [⟨plan5167,[],none,⟨10,10,0⟩⟩]

def t5_1297jobs : List Job := t5_1297jobs0




def t5_1298root : Job := ⟨plan5168,[],none,⟨10,10,0⟩⟩
def t5_1298jobs0 : List Job := [⟨plan5168,[],none,⟨10,10,0⟩⟩]

def t5_1298jobs : List Job := t5_1298jobs0




def t5_1299root : Job := ⟨plan3975,[],none,⟨10,1,0⟩⟩
def t5_1299jobs0 : List Job := [⟨plan3975,[],none,⟨10,1,0⟩⟩]

def t5_1299jobs : List Job := t5_1299jobs0




def t5_1300root : Job := ⟨plan4385,[],none,⟨10,3,0⟩⟩
def t5_1300jobs0 : List Job := [⟨plan2859,[⟨5,0,2⟩],(some ⟨5,0,2⟩),⟨10,1,(-2)⟩⟩,⟨plan2859,[⟨5,1,1⟩],(some ⟨5,1,1⟩),⟨9,2,0⟩⟩,⟨plan2859,[⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨9,1,(-1)⟩⟩,⟨plan2859,[⟨5,2,0⟩],(some ⟨5,2,0⟩),⟨8,3,2⟩⟩]

def t5_1300jobs1 : List Job := [⟨plan2859,[⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨8,2,1⟩⟩,⟨plan2859,[⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨8,1,0⟩⟩]

def t5_1300jobs : List Job := t5_1300jobs0++t5_1300jobs1




def t5_1301root : Job := ⟨plan4386,[],none,⟨10,3,0⟩⟩
def t5_1301jobs0 : List Job := [⟨plan2860,[⟨5,0,2⟩],(some ⟨5,0,2⟩),⟨10,1,(-2)⟩⟩,⟨plan2860,[⟨5,1,1⟩],(some ⟨5,1,1⟩),⟨9,2,0⟩⟩,⟨plan2860,[⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨9,1,(-1)⟩⟩]

def t5_1301jobs1 : List Job := [⟨plan2860,[⟨5,2,0⟩],(some ⟨5,2,0⟩),⟨8,3,2⟩⟩,⟨plan2860,[⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨8,2,1⟩⟩]

def t5_1301jobs2 : List Job := [⟨plan2860,[⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨8,1,0⟩⟩]

def t5_1301jobs : List Job := t5_1301jobs0++t5_1301jobs1++t5_1301jobs2




def t5_1302root : Job := ⟨plan4387,[],none,⟨10,3,0⟩⟩
def t5_1302jobs0 : List Job := [⟨plan2861,[⟨5,0,2⟩],(some ⟨5,0,2⟩),⟨10,1,(-2)⟩⟩,⟨plan2861,[⟨5,1,1⟩],(some ⟨5,1,1⟩),⟨9,2,0⟩⟩,⟨plan2861,[⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨9,1,(-1)⟩⟩,⟨plan2861,[⟨5,2,0⟩],(some ⟨5,2,0⟩),⟨8,3,2⟩⟩]

def t5_1302jobs1 : List Job := [⟨plan2861,[⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨8,2,1⟩⟩,⟨plan2861,[⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨8,1,0⟩⟩]

def t5_1302jobs : List Job := t5_1302jobs0++t5_1302jobs1




def t5_1303root : Job := ⟨plan4882,[],none,⟨10,6,0⟩⟩
def t5_1303jobs0 : List Job := [⟨plan4882,[],none,⟨10,6,0⟩⟩]

def t5_1303jobs : List Job := t5_1303jobs0




def t5_1304root : Job := ⟨plan4883,[],none,⟨10,6,0⟩⟩
def t5_1304jobs0 : List Job := [⟨plan3078,[⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan3078,[⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨9,4,(-1)⟩⟩,⟨plan3078,[⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨9,3,(-2)⟩⟩]

def t5_1304jobs1 : List Job := [⟨plan3078,[⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨8,5,1⟩⟩]

def t5_1304jobs2 : List Job := [⟨plan3078,[⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨8,4,0⟩⟩]

def t5_1304jobs : List Job := t5_1304jobs0++t5_1304jobs1++t5_1304jobs2




def t5_1305root : Job := ⟨plan4884,[],none,⟨10,6,0⟩⟩
def t5_1305jobs0 : List Job := [⟨plan3079,[⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan3079,[⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨9,4,(-1)⟩⟩,⟨plan3079,[⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨9,3,(-2)⟩⟩]

def t5_1305jobs1 : List Job := [⟨plan3079,[⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨8,5,1⟩⟩,⟨plan3079,[⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨8,4,0⟩⟩]

def t5_1305jobs : List Job := t5_1305jobs0++t5_1305jobs1




def t5_1306root : Job := ⟨plan4885,[],none,⟨10,6,0⟩⟩
def t5_1306jobs0 : List Job := [⟨plan3080,[⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan3080,[⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨9,4,(-1)⟩⟩,⟨plan3080,[⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨9,3,(-2)⟩⟩]

def t5_1306jobs1 : List Job := [⟨plan3080,[⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨8,5,1⟩⟩,⟨plan3080,[⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨8,4,0⟩⟩]

def t5_1306jobs : List Job := t5_1306jobs0++t5_1306jobs1



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


