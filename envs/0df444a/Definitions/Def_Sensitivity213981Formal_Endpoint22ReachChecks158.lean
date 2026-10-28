-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks158
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks158
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:32:30.532321+00:00
-- url     : https://prove2.me/theorems/3fee67d7-cb04-49ec-88b5-e5cfd872eb04
-- title:
--   Endpoint22 Reach Checks158 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks158 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t7_127jobs2`, `ThreeBoundEndpoint22Reachable.t7_137root`, `ThreeBoundEndpoint22Reachable.t7_137jobs0`, `ThreeBoundEndpoint22Reachable.t7_137jobs`, `ThreeBoundEndpoint22Reachable.t7_138root`, `ThreeBoundEndpoint22Reachable.t7_138jobs0`, `ThreeBoundEndpoint22Reachable.t7_138jobs`, `ThreeBoundEndpoint22Reachable.t7_139root`, `ThreeBoundEndpoint22Reachable.t7_139jobs0`, `ThreeBoundEndpoint22Reachable.t7_139jobs1`, `ThreeBoundEndpoint22Reachable.t7_139jobs`, `ThreeBoundEndpoint22Reachable.t7_127jobs`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks158.lean, lines 1–272.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans088
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans089
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

def t7_127root : Job := ⟨plan8486,[],none,⟨21,6,0⟩⟩
def t7_127jobs0 : List Job := [⟨plan8109,[⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨21,6,(-4)⟩⟩,⟨plan8109,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨20,6,(-3)⟩⟩,⟨plan8109,[⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨20,6,(-4)⟩⟩]

def t7_127jobs1 : List Job := [⟨plan8109,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨19,6,(-2)⟩⟩]

def t7_127jobs2 : List Job := [⟨plan8109,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨19,6,(-3)⟩⟩,⟨plan8109,[⟨2,2,4⟩],(some ⟨2,2,4⟩),⟨19,6,(-4)⟩⟩]

def t7_127jobs : List Job := t7_127jobs0++t7_127jobs1++t7_127jobs2




def t7_128root : Job := ⟨plan8487,[],none,⟨21,6,0⟩⟩
def t7_128jobs0 : List Job := [⟨plan8110,[⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨21,6,(-4)⟩⟩,⟨plan8110,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨20,6,(-3)⟩⟩,⟨plan8110,[⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨20,6,(-4)⟩⟩,⟨plan8110,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨19,6,(-2)⟩⟩]

def t7_128jobs1 : List Job := [⟨plan8110,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨19,6,(-3)⟩⟩,⟨plan8110,[⟨2,2,4⟩],(some ⟨2,2,4⟩),⟨19,6,(-4)⟩⟩]

def t7_128jobs : List Job := t7_128jobs0++t7_128jobs1




def t7_129root : Job := ⟨plan8488,[],none,⟨21,6,0⟩⟩
def t7_129jobs0 : List Job := [⟨plan8111,[⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨21,6,(-4)⟩⟩,⟨plan8111,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨20,6,(-3)⟩⟩,⟨plan8111,[⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨20,6,(-4)⟩⟩]

def t7_129jobs1 : List Job := [⟨plan8111,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨19,6,(-2)⟩⟩]

def t7_129jobs2 : List Job := [⟨plan8111,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨19,6,(-3)⟩⟩,⟨plan8111,[⟨2,2,4⟩],(some ⟨2,2,4⟩),⟨19,6,(-4)⟩⟩]

def t7_129jobs : List Job := t7_129jobs0++t7_129jobs1++t7_129jobs2




def t7_130root : Job := ⟨plan8489,[],none,⟨21,6,0⟩⟩
def t7_130jobs0 : List Job := [⟨plan8112,[⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨21,6,(-4)⟩⟩,⟨plan8112,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨20,6,(-3)⟩⟩,⟨plan8112,[⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨20,6,(-4)⟩⟩]

def t7_130jobs1 : List Job := [⟨plan8112,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨19,6,(-2)⟩⟩]

def t7_130jobs2 : List Job := [⟨plan8112,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨19,6,(-3)⟩⟩,⟨plan8112,[⟨2,2,4⟩],(some ⟨2,2,4⟩),⟨19,6,(-4)⟩⟩]

def t7_130jobs : List Job := t7_130jobs0++t7_130jobs1++t7_130jobs2




def t7_131root : Job := ⟨plan8490,[],none,⟨21,6,0⟩⟩
def t7_131jobs0 : List Job := [⟨plan8490,[],none,⟨21,6,0⟩⟩]

def t7_131jobs : List Job := t7_131jobs0




def t7_132root : Job := ⟨plan8491,[],none,⟨21,6,0⟩⟩
def t7_132jobs0 : List Job := [⟨plan8491,[],none,⟨21,6,0⟩⟩]

def t7_132jobs : List Job := t7_132jobs0




def t7_133root : Job := ⟨plan8588,[],none,⟨21,10,0⟩⟩
def t7_133jobs0 : List Job := [⟨plan8588,[],none,⟨21,10,0⟩⟩]

def t7_133jobs : List Job := t7_133jobs0




def t7_134root : Job := ⟨plan8589,[],none,⟨21,10,0⟩⟩
def t7_134jobs0 : List Job := [⟨plan8589,[],none,⟨21,10,0⟩⟩]

def t7_134jobs : List Job := t7_134jobs0




def t7_135root : Job := ⟨plan8590,[],none,⟨21,10,0⟩⟩
def t7_135jobs0 : List Job := [⟨plan8590,[],none,⟨21,10,0⟩⟩]

def t7_135jobs : List Job := t7_135jobs0




def t7_136root : Job := ⟨plan8591,[],none,⟨21,10,0⟩⟩
def t7_136jobs0 : List Job := [⟨plan8591,[],none,⟨21,10,0⟩⟩]

def t7_136jobs : List Job := t7_136jobs0




def t7_137root : Job := ⟨plan8592,[],none,⟨21,10,0⟩⟩
def t7_137jobs0 : List Job := [⟨plan8592,[],none,⟨21,10,0⟩⟩]

def t7_137jobs : List Job := t7_137jobs0




def t7_138root : Job := ⟨plan8593,[],none,⟨21,10,0⟩⟩
def t7_138jobs0 : List Job := [⟨plan8593,[],none,⟨21,10,0⟩⟩]

def t7_138jobs : List Job := t7_138jobs0




def t7_139root : Job := ⟨plan8594,[],none,⟨21,10,0⟩⟩
def t7_139jobs0 : List Job := [⟨plan8158,[⟨2,0,5⟩],(some ⟨2,0,5⟩),⟨21,10,(-5)⟩⟩,⟨plan8158,[⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨20,10,(-4)⟩⟩,⟨plan8158,[⟨2,1,5⟩],(some ⟨2,1,5⟩),⟨20,10,(-5)⟩⟩]

def t7_139jobs1 : List Job := [⟨plan8158,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨19,10,(-3)⟩⟩,⟨plan8158,[⟨2,2,4⟩],(some ⟨2,2,4⟩),⟨19,10,(-4)⟩⟩]

def t7_139jobs : List Job := t7_139jobs0++t7_139jobs1




def t7_140root : Job := ⟨plan8595,[],none,⟨21,10,0⟩⟩
def t7_140jobs0 : List Job := [⟨plan8595,[],none,⟨21,10,0⟩⟩]

def t7_140jobs : List Job := t7_140jobs0




def t7_141root : Job := ⟨plan8596,[],none,⟨21,10,0⟩⟩
def t7_141jobs0 : List Job := [⟨plan8596,[],none,⟨21,10,0⟩⟩]

def t7_141jobs : List Job := t7_141jobs0




def t7_142root : Job := ⟨plan8597,[],none,⟨21,10,0⟩⟩
def t7_142jobs0 : List Job := [⟨plan8597,[],none,⟨21,10,0⟩⟩]

def t7_142jobs : List Job := t7_142jobs0




def t7_143root : Job := ⟨plan8492,[],none,⟨21,6,0⟩⟩
def t7_143jobs0 : List Job := [⟨plan8492,[],none,⟨21,6,0⟩⟩]

def t7_143jobs : List Job := t7_143jobs0




def t7_144root : Job := ⟨plan8598,[],none,⟨21,10,0⟩⟩
def t7_144jobs0 : List Job := [⟨plan8598,[],none,⟨21,10,0⟩⟩]

def t7_144jobs : List Job := t7_144jobs0




def t7_145root : Job := ⟨plan8599,[],none,⟨21,10,0⟩⟩
def t7_145jobs0 : List Job := [⟨plan8599,[],none,⟨21,10,0⟩⟩]

def t7_145jobs : List Job := t7_145jobs0




def t7_146root : Job := ⟨plan8600,[],none,⟨21,10,0⟩⟩
def t7_146jobs0 : List Job := [⟨plan8600,[],none,⟨21,10,0⟩⟩]

def t7_146jobs : List Job := t7_146jobs0




def t7_147root : Job := ⟨plan8601,[],none,⟨21,10,0⟩⟩
def t7_147jobs0 : List Job := [⟨plan8165,[⟨2,0,5⟩],(some ⟨2,0,5⟩),⟨21,10,(-5)⟩⟩,⟨plan8165,[⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨20,10,(-4)⟩⟩,⟨plan8165,[⟨2,1,5⟩],(some ⟨2,1,5⟩),⟨20,10,(-5)⟩⟩]

def t7_147jobs1 : List Job := [⟨plan8165,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨19,10,(-3)⟩⟩,⟨plan8165,[⟨2,2,4⟩],(some ⟨2,2,4⟩),⟨19,10,(-4)⟩⟩]

def t7_147jobs : List Job := t7_147jobs0++t7_147jobs1




def t7_148root : Job := ⟨plan8602,[],none,⟨21,10,0⟩⟩
def t7_148jobs0 : List Job := [⟨plan8602,[],none,⟨21,10,0⟩⟩]

def t7_148jobs : List Job := t7_148jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


