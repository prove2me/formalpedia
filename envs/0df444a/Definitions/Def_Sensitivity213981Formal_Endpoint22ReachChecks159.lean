-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks159
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks159
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:33:13.769248+00:00
-- url     : https://prove2.me/theorems/20fc13bb-d455-449f-99a2-175a4c75496d
-- title:
--   Endpoint22 Reach Checks159 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks159 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t7_158jobs`, `ThreeBoundEndpoint22Reachable.t7_159root`, `ThreeBoundEndpoint22Reachable.t7_159jobs0`, `ThreeBoundEndpoint22Reachable.t7_159jobs`, `ThreeBoundEndpoint22Reachable.t7_160root`, `ThreeBoundEndpoint22Reachable.t7_160jobs0`, `ThreeBoundEndpoint22Reachable.t7_160jobs`, `ThreeBoundEndpoint22Reachable.t7_150root`, `ThreeBoundEndpoint22Reachable.t7_150jobs0`, `ThreeBoundEndpoint22Reachable.t7_150jobs`, `ThreeBoundEndpoint22Reachable.t7_151root`, `ThreeBoundEndpoint22Reachable.t7_151jobs0`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks159.lean, lines 1–165.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans087
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

def t7_149root : Job := ⟨plan8603,[],none,⟨21,10,0⟩⟩
def t7_149jobs0 : List Job := [⟨plan8603,[],none,⟨21,10,0⟩⟩]

def t7_149jobs : List Job := t7_149jobs0




def t7_150root : Job := ⟨plan8413,[],none,⟨21,0,0⟩⟩
def t7_150jobs0 : List Job := [⟨plan8413,[],none,⟨21,0,0⟩⟩]

def t7_150jobs : List Job := t7_150jobs0




def t7_151root : Job := ⟨plan8419,[],none,⟨21,1,0⟩⟩
def t7_151jobs0 : List Job := [⟨plan8419,[],none,⟨21,1,0⟩⟩]

def t7_151jobs : List Job := t7_151jobs0




def t7_152root : Job := ⟨plan8420,[],none,⟨21,1,0⟩⟩
def t7_152jobs0 : List Job := [⟨plan8420,[],none,⟨21,1,0⟩⟩]

def t7_152jobs : List Job := t7_152jobs0




def t7_153root : Job := ⟨plan8421,[],none,⟨21,1,0⟩⟩
def t7_153jobs0 : List Job := [⟨plan8421,[],none,⟨21,1,0⟩⟩]

def t7_153jobs : List Job := t7_153jobs0




def t7_154root : Job := ⟨plan8439,[],none,⟨21,3,0⟩⟩
def t7_154jobs0 : List Job := [⟨plan8439,[],none,⟨21,3,0⟩⟩]

def t7_154jobs : List Job := t7_154jobs0




def t7_155root : Job := ⟨plan8440,[],none,⟨21,3,0⟩⟩
def t7_155jobs0 : List Job := [⟨plan8094,[⟨2,0,3⟩],(some ⟨2,0,3⟩),⟨21,3,(-3)⟩⟩,⟨plan8094,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨20,3,(-2)⟩⟩,⟨plan8094,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨20,3,(-3)⟩⟩]

def t7_155jobs1 : List Job := [⟨plan8094,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨19,3,(-1)⟩⟩]

def t7_155jobs2 : List Job := [⟨plan8094,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨19,3,(-2)⟩⟩]

def t7_155jobs3 : List Job := [⟨plan8094,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨19,3,(-3)⟩⟩]

def t7_155jobs : List Job := t7_155jobs0++t7_155jobs1++t7_155jobs2++t7_155jobs3




def t7_156root : Job := ⟨plan8441,[],none,⟨21,3,0⟩⟩
def t7_156jobs0 : List Job := [⟨plan8095,[⟨2,0,3⟩],(some ⟨2,0,3⟩),⟨21,3,(-3)⟩⟩,⟨plan8095,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨20,3,(-2)⟩⟩,⟨plan8095,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨20,3,(-3)⟩⟩,⟨plan8095,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨19,3,(-1)⟩⟩,⟨plan8095,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨19,3,(-2)⟩⟩]

def t7_156jobs1 : List Job := [⟨plan8095,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨19,3,(-3)⟩⟩]

def t7_156jobs : List Job := t7_156jobs0++t7_156jobs1




def t7_157root : Job := ⟨plan8442,[],none,⟨21,3,0⟩⟩
def t7_157jobs0 : List Job := [⟨plan8097,[⟨2,0,3⟩],(some ⟨2,0,3⟩),⟨21,3,(-3)⟩⟩,⟨plan8097,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨20,3,(-2)⟩⟩,⟨plan8097,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨20,3,(-3)⟩⟩]

def t7_157jobs1 : List Job := [⟨plan8097,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨19,3,(-1)⟩⟩]

def t7_157jobs2 : List Job := [⟨plan8097,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨19,3,(-2)⟩⟩]

def t7_157jobs3 : List Job := [⟨plan8097,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨19,3,(-3)⟩⟩]

def t7_157jobs : List Job := t7_157jobs0++t7_157jobs1++t7_157jobs2++t7_157jobs3




def t7_158root : Job := ⟨plan8443,[],none,⟨21,3,0⟩⟩
def t7_158jobs0 : List Job := [⟨plan8098,[⟨2,0,3⟩],(some ⟨2,0,3⟩),⟨21,3,(-3)⟩⟩,⟨plan8098,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨20,3,(-2)⟩⟩,⟨plan8098,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨20,3,(-3)⟩⟩]

def t7_158jobs1 : List Job := [⟨plan8098,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨19,3,(-1)⟩⟩]

def t7_158jobs2 : List Job := [⟨plan8098,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨19,3,(-2)⟩⟩]

def t7_158jobs3 : List Job := [⟨plan8098,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨19,3,(-3)⟩⟩]

def t7_158jobs : List Job := t7_158jobs0++t7_158jobs1++t7_158jobs2++t7_158jobs3




def t7_159root : Job := ⟨plan8444,[],none,⟨21,3,0⟩⟩
def t7_159jobs0 : List Job := [⟨plan8444,[],none,⟨21,3,0⟩⟩]

def t7_159jobs : List Job := t7_159jobs0




def t7_160root : Job := ⟨plan8493,[],none,⟨21,6,0⟩⟩
def t7_160jobs0 : List Job := [⟨plan8493,[],none,⟨21,6,0⟩⟩]

def t7_160jobs : List Job := t7_160jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


