-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks166
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks166
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:33:25.156362+00:00
-- url     : https://prove2.me/theorems/a6cd9f69-b043-4da1-9878-d7c48305f06a
-- title:
--   Endpoint22 Reach Checks166 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks166 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t7_196jobs0`, `ThreeBoundEndpoint22Reachable.t7_196jobs`, `ThreeBoundEndpoint22Reachable.t7_197root`, `ThreeBoundEndpoint22Reachable.t7_197jobs0`, `ThreeBoundEndpoint22Reachable.t7_197jobs`, `ThreeBoundEndpoint22Reachable.t7_187jobs2`, `ThreeBoundEndpoint22Reachable.t7_198root`, `ThreeBoundEndpoint22Reachable.t7_198jobs0`, `ThreeBoundEndpoint22Reachable.t7_198jobs`, `ThreeBoundEndpoint22Reachable.t7_199root`, `ThreeBoundEndpoint22Reachable.t7_199jobs0`, `ThreeBoundEndpoint22Reachable.t7_199jobs`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks166.lean, lines 1–229.

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

def t7_187root : Job := ⟨plan8504,[],none,⟨21,6,0⟩⟩
def t7_187jobs0 : List Job := [⟨plan8139,[⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨21,6,(-4)⟩⟩,⟨plan8139,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨20,6,(-3)⟩⟩,⟨plan8139,[⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨20,6,(-4)⟩⟩,⟨plan8139,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨19,6,(-2)⟩⟩]

def t7_187jobs1 : List Job := [⟨plan8139,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨19,6,(-3)⟩⟩]

def t7_187jobs2 : List Job := [⟨plan8139,[⟨2,2,4⟩],(some ⟨2,2,4⟩),⟨19,6,(-4)⟩⟩]

def t7_187jobs : List Job := t7_187jobs0++t7_187jobs1++t7_187jobs2




def t7_188root : Job := ⟨plan8505,[],none,⟨21,6,0⟩⟩
def t7_188jobs0 : List Job := [⟨plan8140,[⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨21,6,(-4)⟩⟩,⟨plan8140,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨20,6,(-3)⟩⟩,⟨plan8140,[⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨20,6,(-4)⟩⟩,⟨plan8140,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨19,6,(-2)⟩⟩,⟨plan8140,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨19,6,(-3)⟩⟩]

def t7_188jobs1 : List Job := [⟨plan8140,[⟨2,2,4⟩],(some ⟨2,2,4⟩),⟨19,6,(-4)⟩⟩]

def t7_188jobs : List Job := t7_188jobs0++t7_188jobs1




def t7_189root : Job := ⟨plan8619,[],none,⟨21,10,0⟩⟩
def t7_189jobs0 : List Job := [⟨plan8619,[],none,⟨21,10,0⟩⟩]

def t7_189jobs : List Job := t7_189jobs0




def t7_190root : Job := ⟨plan8620,[],none,⟨21,10,0⟩⟩
def t7_190jobs0 : List Job := [⟨plan8204,[⟨2,0,5⟩],(some ⟨2,0,5⟩),⟨21,10,(-5)⟩⟩,⟨plan8204,[⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨20,10,(-4)⟩⟩,⟨plan8204,[⟨2,1,5⟩],(some ⟨2,1,5⟩),⟨20,10,(-5)⟩⟩]

def t7_190jobs1 : List Job := [⟨plan8204,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨19,10,(-3)⟩⟩]

def t7_190jobs2 : List Job := [⟨plan8204,[⟨2,2,4⟩],(some ⟨2,2,4⟩),⟨19,10,(-4)⟩⟩]

def t7_190jobs : List Job := t7_190jobs0++t7_190jobs1++t7_190jobs2




def t7_191root : Job := ⟨plan8621,[],none,⟨21,10,0⟩⟩
def t7_191jobs0 : List Job := [⟨plan8621,[],none,⟨21,10,0⟩⟩]

def t7_191jobs : List Job := t7_191jobs0




def t7_192root : Job := ⟨plan8622,[],none,⟨21,10,0⟩⟩
def t7_192jobs0 : List Job := [⟨plan8206,[⟨2,0,5⟩],(some ⟨2,0,5⟩),⟨21,10,(-5)⟩⟩,⟨plan8206,[⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨20,10,(-4)⟩⟩,⟨plan8206,[⟨2,1,5⟩],(some ⟨2,1,5⟩),⟨20,10,(-5)⟩⟩]

def t7_192jobs1 : List Job := [⟨plan8206,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨19,10,(-3)⟩⟩]

def t7_192jobs2 : List Job := [⟨plan8206,[⟨2,2,4⟩],(some ⟨2,2,4⟩),⟨19,10,(-4)⟩⟩]

def t7_192jobs : List Job := t7_192jobs0++t7_192jobs1++t7_192jobs2




def t7_193root : Job := ⟨plan8623,[],none,⟨21,10,0⟩⟩
def t7_193jobs0 : List Job := [⟨plan8207,[⟨2,0,5⟩],(some ⟨2,0,5⟩),⟨21,10,(-5)⟩⟩,⟨plan8207,[⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨20,10,(-4)⟩⟩,⟨plan8207,[⟨2,1,5⟩],(some ⟨2,1,5⟩),⟨20,10,(-5)⟩⟩]

def t7_193jobs1 : List Job := [⟨plan8207,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨19,10,(-3)⟩⟩]

def t7_193jobs2 : List Job := [⟨plan8207,[⟨2,2,4⟩],(some ⟨2,2,4⟩),⟨19,10,(-4)⟩⟩]

def t7_193jobs : List Job := t7_193jobs0++t7_193jobs1++t7_193jobs2




def t7_194root : Job := ⟨plan8624,[],none,⟨21,10,0⟩⟩
def t7_194jobs0 : List Job := [⟨plan8624,[],none,⟨21,10,0⟩⟩]

def t7_194jobs : List Job := t7_194jobs0




def t7_195root : Job := ⟨plan8625,[],none,⟨21,10,0⟩⟩
def t7_195jobs0 : List Job := [⟨plan8625,[],none,⟨21,10,0⟩⟩]

def t7_195jobs : List Job := t7_195jobs0




def t7_196root : Job := ⟨plan8762,[],none,⟨21,15,0⟩⟩
def t7_196jobs0 : List Job := [⟨plan8762,[],none,⟨21,15,0⟩⟩]

def t7_196jobs : List Job := t7_196jobs0




def t7_197root : Job := ⟨plan8763,[],none,⟨21,15,0⟩⟩
def t7_197jobs0 : List Job := [⟨plan8763,[],none,⟨21,15,0⟩⟩]

def t7_197jobs : List Job := t7_197jobs0




def t7_198root : Job := ⟨plan8764,[],none,⟨21,15,0⟩⟩
def t7_198jobs0 : List Job := [⟨plan8764,[],none,⟨21,15,0⟩⟩]

def t7_198jobs : List Job := t7_198jobs0




def t7_199root : Job := ⟨plan8765,[],none,⟨21,15,0⟩⟩
def t7_199jobs0 : List Job := [⟨plan8765,[],none,⟨21,15,0⟩⟩]

def t7_199jobs : List Job := t7_199jobs0




def t7_200root : Job := ⟨plan8766,[],none,⟨21,15,0⟩⟩
def t7_200jobs0 : List Job := [⟨plan8766,[],none,⟨21,15,0⟩⟩]

def t7_200jobs : List Job := t7_200jobs0




def t7_201root : Job := ⟨plan8767,[],none,⟨21,15,0⟩⟩
def t7_201jobs0 : List Job := [⟨plan8767,[],none,⟨21,15,0⟩⟩]

def t7_201jobs : List Job := t7_201jobs0




def t7_202root : Job := ⟨plan8768,[],none,⟨21,15,0⟩⟩
def t7_202jobs0 : List Job := [⟨plan8768,[],none,⟨21,15,0⟩⟩]

def t7_202jobs : List Job := t7_202jobs0




def t7_203root : Job := ⟨plan8769,[],none,⟨21,15,0⟩⟩
def t7_203jobs0 : List Job := [⟨plan8769,[],none,⟨21,15,0⟩⟩]

def t7_203jobs : List Job := t7_203jobs0




def t7_204root : Job := ⟨plan8770,[],none,⟨21,15,0⟩⟩
def t7_204jobs0 : List Job := [⟨plan8770,[],none,⟨21,15,0⟩⟩]

def t7_204jobs : List Job := t7_204jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


