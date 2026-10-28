-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks017
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks017
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:24:27.661141+00:00
-- url     : https://prove2.me/theorems/bf847243-2934-435d-986f-05a32bd2e68a
-- title:
--   Endpoint22 Reach Checks017 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks017 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t5_739root`, `ThreeBoundEndpoint22Reachable.t5_739jobs0`, `ThreeBoundEndpoint22Reachable.t5_739jobs1`, `ThreeBoundEndpoint22Reachable.t5_739jobs2`, `ThreeBoundEndpoint22Reachable.t5_739jobs`, `ThreeBoundEndpoint22Reachable.t5_740root`, `ThreeBoundEndpoint22Reachable.t5_740jobs0`, `ThreeBoundEndpoint22Reachable.t5_740jobs1`, `ThreeBoundEndpoint22Reachable.t5_729root`, `ThreeBoundEndpoint22Reachable.t5_740jobs2`, `ThreeBoundEndpoint22Reachable.t5_740jobs3`, `ThreeBoundEndpoint22Reachable.t5_740jobs`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks017.lean, lines 1–191.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans038
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans040
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

def t5_728root : Job := ⟨plan4265,[],none,⟨10,3,0⟩⟩
def t5_728jobs0 : List Job := [⟨plan4265,[],none,⟨10,3,0⟩⟩]

def t5_728jobs : List Job := t5_728jobs0




def t5_729root : Job := ⟨plan4266,[],none,⟨10,3,0⟩⟩
def t5_729jobs0 : List Job := [⟨plan4266,[],none,⟨10,3,0⟩⟩]

def t5_729jobs : List Job := t5_729jobs0




def t5_730root : Job := ⟨plan4267,[],none,⟨10,3,0⟩⟩
def t5_730jobs0 : List Job := [⟨plan4267,[],none,⟨10,3,0⟩⟩]

def t5_730jobs : List Job := t5_730jobs0




def t5_731root : Job := ⟨plan4268,[],none,⟨10,3,0⟩⟩
def t5_731jobs0 : List Job := [⟨plan4268,[],none,⟨10,3,0⟩⟩]

def t5_731jobs : List Job := t5_731jobs0




def t5_732root : Job := ⟨plan3672,[],none,⟨10,0,0⟩⟩
def t5_732jobs0 : List Job := [⟨plan3672,[],none,⟨10,0,0⟩⟩]

def t5_732jobs : List Job := t5_732jobs0




def t5_733root : Job := ⟨plan3741,[],none,⟨10,0,0⟩⟩
def t5_733jobs0 : List Job := [⟨plan3741,[],none,⟨10,0,0⟩⟩]

def t5_733jobs : List Job := t5_733jobs0




def t5_734root : Job := ⟨plan3742,[],none,⟨10,0,0⟩⟩
def t5_734jobs0 : List Job := [⟨plan3742,[],none,⟨10,0,0⟩⟩]

def t5_734jobs : List Job := t5_734jobs0




def t5_735root : Job := ⟨plan3743,[],none,⟨10,0,0⟩⟩
def t5_735jobs0 : List Job := [⟨plan3743,[],none,⟨10,0,0⟩⟩]

def t5_735jobs : List Job := t5_735jobs0




def t5_736root : Job := ⟨plan3928,[],none,⟨10,1,0⟩⟩
def t5_736jobs0 : List Job := [⟨plan2630,[⟨2,0,2⟩],(some ⟨2,0,2⟩),⟨10,1,(-2)⟩⟩,⟨plan2630,[⟨2,1,1⟩],(some ⟨2,1,1⟩),⟨9,1,(-1)⟩⟩,⟨plan2630,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨9,1,(-2)⟩⟩,⟨plan2630,[⟨2,2,0⟩],(some ⟨2,2,0⟩),⟨8,1,0⟩⟩]

def t5_736jobs1 : List Job := [⟨plan2630,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨8,1,(-1)⟩⟩,⟨plan2630,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,1,(-2)⟩⟩]

def t5_736jobs : List Job := t5_736jobs0++t5_736jobs1




def t5_737root : Job := ⟨plan3929,[],none,⟨10,1,0⟩⟩
def t5_737jobs0 : List Job := [⟨plan2631,[⟨2,0,2⟩],(some ⟨2,0,2⟩),⟨10,1,(-2)⟩⟩,⟨plan2631,[⟨2,1,1⟩],(some ⟨2,1,1⟩),⟨9,1,(-1)⟩⟩]

def t5_737jobs1 : List Job := [⟨plan2631,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨9,1,(-2)⟩⟩,⟨plan2631,[⟨2,2,0⟩],(some ⟨2,2,0⟩),⟨8,1,0⟩⟩]

def t5_737jobs2 : List Job := [⟨plan2631,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨8,1,(-1)⟩⟩]

def t5_737jobs3 : List Job := [⟨plan2631,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,1,(-2)⟩⟩]

def t5_737jobs : List Job := t5_737jobs0++t5_737jobs1++t5_737jobs2++t5_737jobs3




def t5_738root : Job := ⟨plan3930,[],none,⟨10,1,0⟩⟩
def t5_738jobs0 : List Job := [⟨plan2632,[⟨2,0,2⟩],(some ⟨2,0,2⟩),⟨10,1,(-2)⟩⟩,⟨plan2632,[⟨2,1,1⟩],(some ⟨2,1,1⟩),⟨9,1,(-1)⟩⟩,⟨plan2632,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨9,1,(-2)⟩⟩]

def t5_738jobs1 : List Job := [⟨plan2632,[⟨2,2,0⟩],(some ⟨2,2,0⟩),⟨8,1,0⟩⟩,⟨plan2632,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨8,1,(-1)⟩⟩]

def t5_738jobs2 : List Job := [⟨plan2632,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,1,(-2)⟩⟩]

def t5_738jobs : List Job := t5_738jobs0++t5_738jobs1++t5_738jobs2




def t5_739root : Job := ⟨plan3931,[],none,⟨10,1,0⟩⟩
def t5_739jobs0 : List Job := [⟨plan2633,[⟨2,0,2⟩],(some ⟨2,0,2⟩),⟨10,1,(-2)⟩⟩,⟨plan2633,[⟨2,1,1⟩],(some ⟨2,1,1⟩),⟨9,1,(-1)⟩⟩,⟨plan2633,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨9,1,(-2)⟩⟩]

def t5_739jobs1 : List Job := [⟨plan2633,[⟨2,2,0⟩],(some ⟨2,2,0⟩),⟨8,1,0⟩⟩,⟨plan2633,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨8,1,(-1)⟩⟩]

def t5_739jobs2 : List Job := [⟨plan2633,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,1,(-2)⟩⟩]

def t5_739jobs : List Job := t5_739jobs0++t5_739jobs1++t5_739jobs2




def t5_740root : Job := ⟨plan3932,[],none,⟨10,1,0⟩⟩
def t5_740jobs0 : List Job := [⟨plan2634,[⟨2,0,2⟩],(some ⟨2,0,2⟩),⟨10,1,(-2)⟩⟩,⟨plan2634,[⟨2,1,1⟩],(some ⟨2,1,1⟩),⟨9,1,(-1)⟩⟩]

def t5_740jobs1 : List Job := [⟨plan2634,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨9,1,(-2)⟩⟩,⟨plan2634,[⟨2,2,0⟩],(some ⟨2,2,0⟩),⟨8,1,0⟩⟩]

def t5_740jobs2 : List Job := [⟨plan2634,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨8,1,(-1)⟩⟩]

def t5_740jobs3 : List Job := [⟨plan2634,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,1,(-2)⟩⟩]

def t5_740jobs : List Job := t5_740jobs0++t5_740jobs1++t5_740jobs2++t5_740jobs3




def t5_741root : Job := ⟨plan3933,[],none,⟨10,1,0⟩⟩
def t5_741jobs0 : List Job := [⟨plan2635,[⟨2,0,2⟩],(some ⟨2,0,2⟩),⟨10,1,(-2)⟩⟩,⟨plan2635,[⟨2,1,1⟩],(some ⟨2,1,1⟩),⟨9,1,(-1)⟩⟩,⟨plan2635,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨9,1,(-2)⟩⟩,⟨plan2635,[⟨2,2,0⟩],(some ⟨2,2,0⟩),⟨8,1,0⟩⟩]

def t5_741jobs1 : List Job := [⟨plan2635,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨8,1,(-1)⟩⟩,⟨plan2635,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,1,(-2)⟩⟩]

def t5_741jobs : List Job := t5_741jobs0++t5_741jobs1



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


