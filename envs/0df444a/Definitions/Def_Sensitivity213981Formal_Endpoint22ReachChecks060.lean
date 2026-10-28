-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks060
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks060
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:25:03.236786+00:00
-- url     : https://prove2.me/theorems/e294bb55-5176-4f3d-9268-23fcce1f27ce
-- title:
--   Endpoint22 Reach Checks060 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks060 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_469jobs`, `ThreeBoundEndpoint22Reachable.t6_477root`, `ThreeBoundEndpoint22Reachable.t6_477jobs0`, `ThreeBoundEndpoint22Reachable.t6_477jobs1`, `ThreeBoundEndpoint22Reachable.t6_477jobs2`, `ThreeBoundEndpoint22Reachable.t6_477jobs`, `ThreeBoundEndpoint22Reachable.t6_478root`, `ThreeBoundEndpoint22Reachable.t6_478jobs0`, `ThreeBoundEndpoint22Reachable.t6_478jobs1`, `ThreeBoundEndpoint22Reachable.t6_478jobs2`, `ThreeBoundEndpoint22Reachable.t6_478jobs`, `ThreeBoundEndpoint22Reachable.t6_479root`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks060.lean, lines 1–234.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans068
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans071
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans075
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans076
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

def t6_469root : Job := ⟨plan6533,[],none,⟨15,3,0⟩⟩
def t6_469jobs0 : List Job := [⟨plan5530,[⟨1,0,3⟩],(some ⟨1,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5530,[⟨1,1,2⟩],(some ⟨1,1,2⟩),⟨14,3,(-2)⟩⟩]

def t6_469jobs1 : List Job := [⟨plan5530,[⟨1,1,3⟩],(some ⟨1,1,3⟩),⟨14,3,(-3)⟩⟩]

def t6_469jobs : List Job := t6_469jobs0++t6_469jobs1




def t6_470root : Job := ⟨plan6534,[],none,⟨15,3,0⟩⟩
def t6_470jobs0 : List Job := [⟨plan6534,[],none,⟨15,3,0⟩⟩]

def t6_470jobs : List Job := t6_470jobs0




def t6_471root : Job := ⟨plan6857,[],none,⟨15,6,0⟩⟩
def t6_471jobs0 : List Job := [⟨plan6857,[],none,⟨15,6,0⟩⟩]

def t6_471jobs : List Job := t6_471jobs0




def t6_472root : Job := ⟨plan6858,[],none,⟨15,6,0⟩⟩
def t6_472jobs0 : List Job := [⟨plan5721,[⟨1,0,4⟩],(some ⟨1,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5721,[⟨1,1,3⟩],(some ⟨1,1,3⟩),⟨14,6,(-3)⟩⟩]

def t6_472jobs1 : List Job := [⟨plan5721,[⟨1,1,4⟩],(some ⟨1,1,4⟩),⟨14,6,(-4)⟩⟩]

def t6_472jobs : List Job := t6_472jobs0++t6_472jobs1




def t6_473root : Job := ⟨plan6859,[],none,⟨15,6,0⟩⟩
def t6_473jobs0 : List Job := [⟨plan6859,[],none,⟨15,6,0⟩⟩]

def t6_473jobs : List Job := t6_473jobs0




def t6_474root : Job := ⟨plan6860,[],none,⟨15,6,0⟩⟩
def t6_474jobs0 : List Job := [⟨plan3363,[⟨1,0,4⟩,⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨15,3,(-7)⟩⟩,⟨plan3363,[⟨1,0,4⟩,⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨14,4,(-5)⟩⟩,⟨plan3363,[⟨1,0,4⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3363,[⟨1,0,4⟩,⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨13,5,(-3)⟩⟩,⟨plan3363,[⟨1,0,4⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨13,4,(-4)⟩⟩,⟨plan3363,[⟨1,0,4⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3363,[⟨1,1,3⟩,⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3363,[⟨1,1,3⟩,⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨13,4,(-4)⟩⟩,⟨plan3363,[⟨1,1,3⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3363,[⟨1,1,3⟩,⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨12,5,(-2)⟩⟩]

def t6_474jobs1 : List Job := [⟨plan3363,[⟨1,1,3⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨12,4,(-3)⟩⟩,⟨plan3363,[⟨1,1,3⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨12,3,(-4)⟩⟩,⟨plan3363,[⟨1,1,4⟩,⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨14,3,(-7)⟩⟩,⟨plan3363,[⟨1,1,4⟩,⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨13,4,(-5)⟩⟩,⟨plan3363,[⟨1,1,4⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨13,3,(-6)⟩⟩]

def t6_474jobs2 : List Job := [⟨plan3363,[⟨1,1,4⟩,⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨12,5,(-3)⟩⟩,⟨plan3363,[⟨1,1,4⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨12,4,(-4)⟩⟩,⟨plan3363,[⟨1,1,4⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨12,3,(-5)⟩⟩]

def t6_474jobs : List Job := t6_474jobs0++t6_474jobs1++t6_474jobs2




def t6_475root : Job := ⟨plan6861,[],none,⟨15,6,0⟩⟩
def t6_475jobs0 : List Job := [⟨plan3364,[⟨1,0,4⟩,⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨15,3,(-7)⟩⟩,⟨plan3364,[⟨1,0,4⟩,⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨14,4,(-5)⟩⟩,⟨plan3364,[⟨1,0,4⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3364,[⟨1,0,4⟩,⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨13,5,(-3)⟩⟩,⟨plan3364,[⟨1,0,4⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨13,4,(-4)⟩⟩,⟨plan3364,[⟨1,0,4⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3364,[⟨1,1,3⟩,⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3364,[⟨1,1,3⟩,⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨13,4,(-4)⟩⟩,⟨plan3364,[⟨1,1,3⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3364,[⟨1,1,3⟩,⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨12,5,(-2)⟩⟩,⟨plan3364,[⟨1,1,3⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨12,4,(-3)⟩⟩]

def t6_475jobs1 : List Job := [⟨plan3364,[⟨1,1,3⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨12,3,(-4)⟩⟩,⟨plan3364,[⟨1,1,4⟩,⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨14,3,(-7)⟩⟩,⟨plan3364,[⟨1,1,4⟩,⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨13,4,(-5)⟩⟩,⟨plan3364,[⟨1,1,4⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨13,3,(-6)⟩⟩,⟨plan3364,[⟨1,1,4⟩,⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨12,5,(-3)⟩⟩]

def t6_475jobs2 : List Job := [⟨plan3364,[⟨1,1,4⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨12,4,(-4)⟩⟩,⟨plan3364,[⟨1,1,4⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨12,3,(-5)⟩⟩]

def t6_475jobs : List Job := t6_475jobs0++t6_475jobs1++t6_475jobs2




def t6_476root : Job := ⟨plan6862,[],none,⟨15,6,0⟩⟩
def t6_476jobs0 : List Job := [⟨plan6862,[],none,⟨15,6,0⟩⟩]

def t6_476jobs : List Job := t6_476jobs0




def t6_477root : Job := ⟨plan6863,[],none,⟨15,6,0⟩⟩
def t6_477jobs0 : List Job := [⟨plan5726,[⟨1,0,4⟩],(some ⟨1,0,4⟩),⟨15,6,(-4)⟩⟩]

def t6_477jobs1 : List Job := [⟨plan5726,[⟨1,1,3⟩],(some ⟨1,1,3⟩),⟨14,6,(-3)⟩⟩]

def t6_477jobs2 : List Job := [⟨plan5726,[⟨1,1,4⟩],(some ⟨1,1,4⟩),⟨14,6,(-4)⟩⟩]

def t6_477jobs : List Job := t6_477jobs0++t6_477jobs1++t6_477jobs2




def t6_478root : Job := ⟨plan6864,[],none,⟨15,6,0⟩⟩
def t6_478jobs0 : List Job := [⟨plan3367,[⟨1,0,4⟩,⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨15,3,(-7)⟩⟩,⟨plan3367,[⟨1,0,4⟩,⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨14,4,(-5)⟩⟩,⟨plan3367,[⟨1,0,4⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3367,[⟨1,0,4⟩,⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨13,5,(-3)⟩⟩,⟨plan3367,[⟨1,0,4⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨13,4,(-4)⟩⟩,⟨plan3367,[⟨1,0,4⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3367,[⟨1,1,3⟩,⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3367,[⟨1,1,3⟩,⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨13,4,(-4)⟩⟩,⟨plan3367,[⟨1,1,3⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3367,[⟨1,1,3⟩,⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨12,5,(-2)⟩⟩]

def t6_478jobs1 : List Job := [⟨plan3367,[⟨1,1,3⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨12,4,(-3)⟩⟩,⟨plan3367,[⟨1,1,3⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨12,3,(-4)⟩⟩,⟨plan3367,[⟨1,1,4⟩,⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨14,3,(-7)⟩⟩,⟨plan3367,[⟨1,1,4⟩,⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨13,4,(-5)⟩⟩,⟨plan3367,[⟨1,1,4⟩,⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨13,3,(-6)⟩⟩]

def t6_478jobs2 : List Job := [⟨plan3367,[⟨1,1,4⟩,⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨12,5,(-3)⟩⟩,⟨plan3367,[⟨1,1,4⟩,⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨12,4,(-4)⟩⟩,⟨plan3367,[⟨1,1,4⟩,⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨12,3,(-5)⟩⟩]

def t6_478jobs : List Job := t6_478jobs0++t6_478jobs1++t6_478jobs2




def t6_479root : Job := ⟨plan6865,[],none,⟨15,6,0⟩⟩
def t6_479jobs0 : List Job := [⟨plan5728,[⟨1,0,4⟩],(some ⟨1,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5728,[⟨1,1,3⟩],(some ⟨1,1,3⟩),⟨14,6,(-3)⟩⟩]

def t6_479jobs1 : List Job := [⟨plan5728,[⟨1,1,4⟩],(some ⟨1,1,4⟩),⟨14,6,(-4)⟩⟩]

def t6_479jobs : List Job := t6_479jobs0++t6_479jobs1




def t6_480root : Job := ⟨plan6866,[],none,⟨15,6,0⟩⟩
def t6_480jobs0 : List Job := [⟨plan6866,[],none,⟨15,6,0⟩⟩]

def t6_480jobs : List Job := t6_480jobs0




def t6_481root : Job := ⟨plan7293,[],none,⟨15,10,0⟩⟩
def t6_481jobs0 : List Job := [⟨plan7293,[],none,⟨15,10,0⟩⟩]

def t6_481jobs : List Job := t6_481jobs0




def t6_482root : Job := ⟨plan7294,[],none,⟨15,10,0⟩⟩
def t6_482jobs0 : List Job := [⟨plan7294,[],none,⟨15,10,0⟩⟩]

def t6_482jobs : List Job := t6_482jobs0




def t6_483root : Job := ⟨plan7295,[],none,⟨15,10,0⟩⟩
def t6_483jobs0 : List Job := [⟨plan7295,[],none,⟨15,10,0⟩⟩]

def t6_483jobs : List Job := t6_483jobs0




def t6_484root : Job := ⟨plan7296,[],none,⟨15,10,0⟩⟩
def t6_484jobs0 : List Job := [⟨plan7296,[],none,⟨15,10,0⟩⟩]

def t6_484jobs : List Job := t6_484jobs0




def t6_485root : Job := ⟨plan7297,[],none,⟨15,10,0⟩⟩
def t6_485jobs0 : List Job := [⟨plan7297,[],none,⟨15,10,0⟩⟩]

def t6_485jobs : List Job := t6_485jobs0




def t6_486root : Job := ⟨plan7298,[],none,⟨15,10,0⟩⟩
def t6_486jobs0 : List Job := [⟨plan7298,[],none,⟨15,10,0⟩⟩]

def t6_486jobs : List Job := t6_486jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


