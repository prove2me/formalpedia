-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks057
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks057
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:27:19.535176+00:00
-- url     : https://prove2.me/theorems/71a9010d-c41f-4bd5-ac18-cf9affd9948e
-- title:
--   Endpoint22 Reach Checks057 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks057 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_369root`, `ThreeBoundEndpoint22Reachable.t6_369jobs0`, `ThreeBoundEndpoint22Reachable.t6_369jobs`, `ThreeBoundEndpoint22Reachable.t6_370root`, `ThreeBoundEndpoint22Reachable.t6_370jobs0`, `ThreeBoundEndpoint22Reachable.t6_370jobs1`, `ThreeBoundEndpoint22Reachable.t6_370jobs2`, `ThreeBoundEndpoint22Reachable.t6_370jobs`, `ThreeBoundEndpoint22Reachable.t6_371root`, `ThreeBoundEndpoint22Reachable.t6_371jobs0`, `ThreeBoundEndpoint22Reachable.t6_371jobs1`, `ThreeBoundEndpoint22Reachable.t6_371jobs2`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks057.lean, lines 1–179.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans067
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans071
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

def t6_361root : Job := ⟨plan6520,[],none,⟨15,3,0⟩⟩
def t6_361jobs0 : List Job := [⟨plan5507,[⟨1,0,3⟩],(some ⟨1,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5507,[⟨1,1,2⟩],(some ⟨1,1,2⟩),⟨14,3,(-2)⟩⟩]

def t6_361jobs1 : List Job := [⟨plan5507,[⟨1,1,3⟩],(some ⟨1,1,3⟩),⟨14,3,(-3)⟩⟩]

def t6_361jobs : List Job := t6_361jobs0++t6_361jobs1




def t6_362root : Job := ⟨plan6521,[],none,⟨15,3,0⟩⟩
def t6_362jobs0 : List Job := [⟨plan5508,[⟨1,0,3⟩],(some ⟨1,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5508,[⟨1,1,2⟩],(some ⟨1,1,2⟩),⟨14,3,(-2)⟩⟩]

def t6_362jobs1 : List Job := [⟨plan5508,[⟨1,1,3⟩],(some ⟨1,1,3⟩),⟨14,3,(-3)⟩⟩]

def t6_362jobs : List Job := t6_362jobs0++t6_362jobs1




def t6_363root : Job := ⟨plan6522,[],none,⟨15,3,0⟩⟩
def t6_363jobs0 : List Job := [⟨plan6522,[],none,⟨15,3,0⟩⟩]

def t6_363jobs : List Job := t6_363jobs0




def t6_364root : Job := ⟨plan6830,[],none,⟨15,6,0⟩⟩
def t6_364jobs0 : List Job := [⟨plan6830,[],none,⟨15,6,0⟩⟩]

def t6_364jobs : List Job := t6_364jobs0




def t6_365root : Job := ⟨plan6831,[],none,⟨15,6,0⟩⟩
def t6_365jobs0 : List Job := [⟨plan5669,[⟨1,0,4⟩],(some ⟨1,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5669,[⟨1,1,3⟩],(some ⟨1,1,3⟩),⟨14,6,(-3)⟩⟩]

def t6_365jobs1 : List Job := [⟨plan5669,[⟨1,1,4⟩],(some ⟨1,1,4⟩),⟨14,6,(-4)⟩⟩]

def t6_365jobs : List Job := t6_365jobs0++t6_365jobs1




def t6_366root : Job := ⟨plan6832,[],none,⟨15,6,0⟩⟩
def t6_366jobs0 : List Job := [⟨plan6832,[],none,⟨15,6,0⟩⟩]

def t6_366jobs : List Job := t6_366jobs0




def t6_367root : Job := ⟨plan6833,[],none,⟨15,6,0⟩⟩
def t6_367jobs0 : List Job := [⟨plan3363,[⟨1,0,4⟩,⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨15,3,(-7)⟩⟩,⟨plan3363,[⟨1,0,4⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨14,4,(-5)⟩⟩,⟨plan3363,[⟨1,0,4⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3363,[⟨1,0,4⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨13,5,(-3)⟩⟩,⟨plan3363,[⟨1,0,4⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨13,4,(-4)⟩⟩,⟨plan3363,[⟨1,0,4⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3363,[⟨1,1,3⟩,⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3363,[⟨1,1,3⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨13,4,(-4)⟩⟩,⟨plan3363,[⟨1,1,3⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3363,[⟨1,1,3⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨12,5,(-2)⟩⟩]

def t6_367jobs1 : List Job := [⟨plan3363,[⟨1,1,3⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨12,4,(-3)⟩⟩,⟨plan3363,[⟨1,1,3⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨12,3,(-4)⟩⟩,⟨plan3363,[⟨1,1,4⟩,⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨14,3,(-7)⟩⟩,⟨plan3363,[⟨1,1,4⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨13,4,(-5)⟩⟩,⟨plan3363,[⟨1,1,4⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨13,3,(-6)⟩⟩]

def t6_367jobs2 : List Job := [⟨plan3363,[⟨1,1,4⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨12,5,(-3)⟩⟩,⟨plan3363,[⟨1,1,4⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨12,4,(-4)⟩⟩,⟨plan3363,[⟨1,1,4⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨12,3,(-5)⟩⟩]

def t6_367jobs : List Job := t6_367jobs0++t6_367jobs1++t6_367jobs2




def t6_368root : Job := ⟨plan6834,[],none,⟨15,6,0⟩⟩
def t6_368jobs0 : List Job := [⟨plan3364,[⟨1,0,4⟩,⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨15,3,(-7)⟩⟩,⟨plan3364,[⟨1,0,4⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨14,4,(-5)⟩⟩,⟨plan3364,[⟨1,0,4⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3364,[⟨1,0,4⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨13,5,(-3)⟩⟩,⟨plan3364,[⟨1,0,4⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨13,4,(-4)⟩⟩,⟨plan3364,[⟨1,0,4⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3364,[⟨1,1,3⟩,⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3364,[⟨1,1,3⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨13,4,(-4)⟩⟩,⟨plan3364,[⟨1,1,3⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3364,[⟨1,1,3⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨12,5,(-2)⟩⟩,⟨plan3364,[⟨1,1,3⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨12,4,(-3)⟩⟩]

def t6_368jobs1 : List Job := [⟨plan3364,[⟨1,1,3⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨12,3,(-4)⟩⟩,⟨plan3364,[⟨1,1,4⟩,⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨14,3,(-7)⟩⟩,⟨plan3364,[⟨1,1,4⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨13,4,(-5)⟩⟩,⟨plan3364,[⟨1,1,4⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨13,3,(-6)⟩⟩,⟨plan3364,[⟨1,1,4⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨12,5,(-3)⟩⟩]

def t6_368jobs2 : List Job := [⟨plan3364,[⟨1,1,4⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨12,4,(-4)⟩⟩,⟨plan3364,[⟨1,1,4⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨12,3,(-5)⟩⟩]

def t6_368jobs : List Job := t6_368jobs0++t6_368jobs1++t6_368jobs2




def t6_369root : Job := ⟨plan6835,[],none,⟨15,6,0⟩⟩
def t6_369jobs0 : List Job := [⟨plan6835,[],none,⟨15,6,0⟩⟩]

def t6_369jobs : List Job := t6_369jobs0




def t6_370root : Job := ⟨plan6836,[],none,⟨15,6,0⟩⟩
def t6_370jobs0 : List Job := [⟨plan5674,[⟨1,0,4⟩],(some ⟨1,0,4⟩),⟨15,6,(-4)⟩⟩]

def t6_370jobs1 : List Job := [⟨plan5674,[⟨1,1,3⟩],(some ⟨1,1,3⟩),⟨14,6,(-3)⟩⟩]

def t6_370jobs2 : List Job := [⟨plan5674,[⟨1,1,4⟩],(some ⟨1,1,4⟩),⟨14,6,(-4)⟩⟩]

def t6_370jobs : List Job := t6_370jobs0++t6_370jobs1++t6_370jobs2




def t6_371root : Job := ⟨plan6837,[],none,⟨15,6,0⟩⟩
def t6_371jobs0 : List Job := [⟨plan3367,[⟨1,0,4⟩,⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨15,3,(-7)⟩⟩,⟨plan3367,[⟨1,0,4⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨14,4,(-5)⟩⟩,⟨plan3367,[⟨1,0,4⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3367,[⟨1,0,4⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨13,5,(-3)⟩⟩,⟨plan3367,[⟨1,0,4⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨13,4,(-4)⟩⟩,⟨plan3367,[⟨1,0,4⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3367,[⟨1,1,3⟩,⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3367,[⟨1,1,3⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨13,4,(-4)⟩⟩,⟨plan3367,[⟨1,1,3⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3367,[⟨1,1,3⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨12,5,(-2)⟩⟩]

def t6_371jobs1 : List Job := [⟨plan3367,[⟨1,1,3⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨12,4,(-3)⟩⟩,⟨plan3367,[⟨1,1,3⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨12,3,(-4)⟩⟩,⟨plan3367,[⟨1,1,4⟩,⟨5,0,3⟩],(some ⟨5,0,3⟩),⟨14,3,(-7)⟩⟩,⟨plan3367,[⟨1,1,4⟩,⟨5,1,2⟩],(some ⟨5,1,2⟩),⟨13,4,(-5)⟩⟩,⟨plan3367,[⟨1,1,4⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨13,3,(-6)⟩⟩]

def t6_371jobs2 : List Job := [⟨plan3367,[⟨1,1,4⟩,⟨5,2,1⟩],(some ⟨5,2,1⟩),⟨12,5,(-3)⟩⟩,⟨plan3367,[⟨1,1,4⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨12,4,(-4)⟩⟩,⟨plan3367,[⟨1,1,4⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨12,3,(-5)⟩⟩]

def t6_371jobs : List Job := t6_371jobs0++t6_371jobs1++t6_371jobs2




def t6_372root : Job := ⟨plan6838,[],none,⟨15,6,0⟩⟩
def t6_372jobs0 : List Job := [⟨plan5676,[⟨1,0,4⟩],(some ⟨1,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5676,[⟨1,1,3⟩],(some ⟨1,1,3⟩),⟨14,6,(-3)⟩⟩]

def t6_372jobs1 : List Job := [⟨plan5676,[⟨1,1,4⟩],(some ⟨1,1,4⟩),⟨14,6,(-4)⟩⟩]

def t6_372jobs : List Job := t6_372jobs0++t6_372jobs1




def t6_373root : Job := ⟨plan6839,[],none,⟨15,6,0⟩⟩
def t6_373jobs0 : List Job := [⟨plan6839,[],none,⟨15,6,0⟩⟩]

def t6_373jobs : List Job := t6_373jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


