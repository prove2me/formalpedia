-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks068
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks068
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:25:58.314974+00:00
-- url     : https://prove2.me/theorems/e9bccf19-943f-4dfc-bc9c-c09700fb0be4
-- title:
--   Endpoint22 Reach Checks068 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks068 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_638root`, `ThreeBoundEndpoint22Reachable.t6_638jobs0`, `ThreeBoundEndpoint22Reachable.t6_638jobs1`, `ThreeBoundEndpoint22Reachable.t6_638jobs2`, `ThreeBoundEndpoint22Reachable.t6_638jobs3`, `ThreeBoundEndpoint22Reachable.t6_638jobs4`, `ThreeBoundEndpoint22Reachable.t6_638jobs`, `ThreeBoundEndpoint22Reachable.t6_628jobs`, `ThreeBoundEndpoint22Reachable.t6_629root`, `ThreeBoundEndpoint22Reachable.t6_629jobs0`, `ThreeBoundEndpoint22Reachable.t6_629jobs`, `ThreeBoundEndpoint22Reachable.t6_630root`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks068.lean, lines 1–157.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans065
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans066
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans071
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans072
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

def t6_628root : Job := ⟨plan6911,[],none,⟨15,6,0⟩⟩
def t6_628jobs0 : List Job := [⟨plan5619,[⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5619,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨14,6,(-3)⟩⟩,⟨plan5619,[⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨14,6,(-4)⟩⟩]

def t6_628jobs1 : List Job := [⟨plan5619,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨13,6,(-2)⟩⟩,⟨plan5619,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨13,6,(-3)⟩⟩]

def t6_628jobs : List Job := t6_628jobs0++t6_628jobs1




def t6_629root : Job := ⟨plan6912,[],none,⟨15,6,0⟩⟩
def t6_629jobs0 : List Job := [⟨plan6912,[],none,⟨15,6,0⟩⟩]

def t6_629jobs : List Job := t6_629jobs0




def t6_630root : Job := ⟨plan6913,[],none,⟨15,6,0⟩⟩
def t6_630jobs0 : List Job := [⟨plan6913,[],none,⟨15,6,0⟩⟩]

def t6_630jobs : List Job := t6_630jobs0




def t6_631root : Job := ⟨plan6281,[],none,⟨15,0,0⟩⟩
def t6_631jobs0 : List Job := [⟨plan6281,[],none,⟨15,0,0⟩⟩]

def t6_631jobs : List Job := t6_631jobs0




def t6_632root : Job := ⟨plan6306,[],none,⟨15,0,0⟩⟩
def t6_632jobs0 : List Job := [⟨plan6306,[],none,⟨15,0,0⟩⟩]

def t6_632jobs : List Job := t6_632jobs0




def t6_633root : Job := ⟨plan6307,[],none,⟨15,0,0⟩⟩
def t6_633jobs0 : List Job := [⟨plan6307,[],none,⟨15,0,0⟩⟩]

def t6_633jobs : List Job := t6_633jobs0




def t6_634root : Job := ⟨plan6308,[],none,⟨15,0,0⟩⟩
def t6_634jobs0 : List Job := [⟨plan6308,[],none,⟨15,0,0⟩⟩]

def t6_634jobs : List Job := t6_634jobs0




def t6_635root : Job := ⟨plan6386,[],none,⟨15,1,0⟩⟩
def t6_635jobs0 : List Job := [⟨plan5396,[⟨2,0,2⟩],(some ⟨2,0,2⟩),⟨15,1,(-2)⟩⟩,⟨plan5396,[⟨2,1,1⟩],(some ⟨2,1,1⟩),⟨14,1,(-1)⟩⟩,⟨plan5396,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨14,1,(-2)⟩⟩,⟨plan5396,[⟨2,2,0⟩],(some ⟨2,2,0⟩),⟨13,1,0⟩⟩,⟨plan5396,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨13,1,(-1)⟩⟩]

def t6_635jobs1 : List Job := [⟨plan5396,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨13,1,(-2)⟩⟩]

def t6_635jobs : List Job := t6_635jobs0++t6_635jobs1




def t6_636root : Job := ⟨plan6387,[],none,⟨15,1,0⟩⟩
def t6_636jobs0 : List Job := [⟨plan5397,[⟨2,0,2⟩],(some ⟨2,0,2⟩),⟨15,1,(-2)⟩⟩,⟨plan5397,[⟨2,1,1⟩],(some ⟨2,1,1⟩),⟨14,1,(-1)⟩⟩]

def t6_636jobs1 : List Job := [⟨plan5397,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨14,1,(-2)⟩⟩]

def t6_636jobs2 : List Job := [⟨plan5397,[⟨2,2,0⟩],(some ⟨2,2,0⟩),⟨13,1,0⟩⟩]

def t6_636jobs3 : List Job := [⟨plan5397,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨13,1,(-1)⟩⟩]

def t6_636jobs4 : List Job := [⟨plan5397,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨13,1,(-2)⟩⟩]

def t6_636jobs : List Job := t6_636jobs0++t6_636jobs1++t6_636jobs2++t6_636jobs3++t6_636jobs4




def t6_637root : Job := ⟨plan6388,[],none,⟨15,1,0⟩⟩
def t6_637jobs0 : List Job := [⟨plan5398,[⟨2,0,2⟩],(some ⟨2,0,2⟩),⟨15,1,(-2)⟩⟩,⟨plan5398,[⟨2,1,1⟩],(some ⟨2,1,1⟩),⟨14,1,(-1)⟩⟩,⟨plan5398,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨14,1,(-2)⟩⟩,⟨plan5398,[⟨2,2,0⟩],(some ⟨2,2,0⟩),⟨13,1,0⟩⟩]

def t6_637jobs1 : List Job := [⟨plan5398,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨13,1,(-1)⟩⟩,⟨plan5398,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨13,1,(-2)⟩⟩]

def t6_637jobs : List Job := t6_637jobs0++t6_637jobs1




def t6_638root : Job := ⟨plan6389,[],none,⟨15,1,0⟩⟩
def t6_638jobs0 : List Job := [⟨plan5399,[⟨2,0,2⟩],(some ⟨2,0,2⟩),⟨15,1,(-2)⟩⟩,⟨plan5399,[⟨2,1,1⟩],(some ⟨2,1,1⟩),⟨14,1,(-1)⟩⟩]

def t6_638jobs1 : List Job := [⟨plan5399,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨14,1,(-2)⟩⟩]

def t6_638jobs2 : List Job := [⟨plan5399,[⟨2,2,0⟩],(some ⟨2,2,0⟩),⟨13,1,0⟩⟩]

def t6_638jobs3 : List Job := [⟨plan5399,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨13,1,(-1)⟩⟩]

def t6_638jobs4 : List Job := [⟨plan5399,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨13,1,(-2)⟩⟩]

def t6_638jobs : List Job := t6_638jobs0++t6_638jobs1++t6_638jobs2++t6_638jobs3++t6_638jobs4



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


