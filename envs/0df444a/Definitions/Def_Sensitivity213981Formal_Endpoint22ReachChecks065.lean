-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks065
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks065
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:28:12.439508+00:00
-- url     : https://prove2.me/theorems/91940562-9328-4340-a822-76e36e68fcbf
-- title:
--   Endpoint22 Reach Checks065 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks065 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_572jobs2`, `ThreeBoundEndpoint22Reachable.t6_583jobs0`, `ThreeBoundEndpoint22Reachable.t6_583jobs`, `ThreeBoundEndpoint22Reachable.t6_584root`, `ThreeBoundEndpoint22Reachable.t6_584jobs0`, `ThreeBoundEndpoint22Reachable.t6_584jobs1`, `ThreeBoundEndpoint22Reachable.t6_584jobs`, `ThreeBoundEndpoint22Reachable.t6_585root`, `ThreeBoundEndpoint22Reachable.t6_585jobs0`, `ThreeBoundEndpoint22Reachable.t6_585jobs`, `ThreeBoundEndpoint22Reachable.t6_572jobs`, `ThreeBoundEndpoint22Reachable.t6_586root`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks065.lean, lines 1–290.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans068
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

def t6_572root : Job := ⟨plan6566,[],none,⟨15,3,0⟩⟩
def t6_572jobs0 : List Job := [⟨plan5468,[⟨2,0,3⟩],(some ⟨2,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5468,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨14,3,(-2)⟩⟩,⟨plan5468,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨14,3,(-3)⟩⟩]

def t6_572jobs1 : List Job := [⟨plan5468,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨13,3,(-1)⟩⟩]

def t6_572jobs2 : List Job := [⟨plan5468,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨13,3,(-2)⟩⟩,⟨plan5468,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨13,3,(-3)⟩⟩]

def t6_572jobs : List Job := t6_572jobs0++t6_572jobs1++t6_572jobs2




def t6_573root : Job := ⟨plan6567,[],none,⟨15,3,0⟩⟩
def t6_573jobs0 : List Job := [⟨plan6567,[],none,⟨15,3,0⟩⟩]

def t6_573jobs : List Job := t6_573jobs0




def t6_574root : Job := ⟨plan6568,[],none,⟨15,3,0⟩⟩
def t6_574jobs0 : List Job := [⟨plan6568,[],none,⟨15,3,0⟩⟩]

def t6_574jobs : List Job := t6_574jobs0




def t6_575root : Job := ⟨plan6870,[],none,⟨15,6,0⟩⟩
def t6_575jobs0 : List Job := [⟨plan6870,[],none,⟨15,6,0⟩⟩]

def t6_575jobs : List Job := t6_575jobs0




def t6_576root : Job := ⟨plan6871,[],none,⟨15,6,0⟩⟩
def t6_576jobs0 : List Job := [⟨plan6871,[],none,⟨15,6,0⟩⟩]

def t6_576jobs : List Job := t6_576jobs0




def t6_577root : Job := ⟨plan6872,[],none,⟨15,6,0⟩⟩
def t6_577jobs0 : List Job := [⟨plan6872,[],none,⟨15,6,0⟩⟩]

def t6_577jobs : List Job := t6_577jobs0




def t6_578root : Job := ⟨plan6873,[],none,⟨15,6,0⟩⟩
def t6_578jobs0 : List Job := [⟨plan6873,[],none,⟨15,6,0⟩⟩]

def t6_578jobs : List Job := t6_578jobs0




def t6_579root : Job := ⟨plan6874,[],none,⟨15,6,0⟩⟩
def t6_579jobs0 : List Job := [⟨plan6874,[],none,⟨15,6,0⟩⟩]

def t6_579jobs : List Job := t6_579jobs0




def t6_580root : Job := ⟨plan6875,[],none,⟨15,6,0⟩⟩
def t6_580jobs0 : List Job := [⟨plan6875,[],none,⟨15,6,0⟩⟩]

def t6_580jobs : List Job := t6_580jobs0




def t6_581root : Job := ⟨plan6876,[],none,⟨15,6,0⟩⟩
def t6_581jobs0 : List Job := [⟨plan5581,[⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5581,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨14,6,(-3)⟩⟩,⟨plan5581,[⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨14,6,(-4)⟩⟩]

def t6_581jobs1 : List Job := [⟨plan5581,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨13,6,(-2)⟩⟩,⟨plan5581,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨13,6,(-3)⟩⟩]

def t6_581jobs : List Job := t6_581jobs0++t6_581jobs1




def t6_582root : Job := ⟨plan6877,[],none,⟨15,6,0⟩⟩
def t6_582jobs0 : List Job := [⟨plan5582,[⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5582,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨14,6,(-3)⟩⟩,⟨plan5582,[⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨14,6,(-4)⟩⟩]

def t6_582jobs1 : List Job := [⟨plan5582,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨13,6,(-2)⟩⟩,⟨plan5582,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨13,6,(-3)⟩⟩]

def t6_582jobs : List Job := t6_582jobs0++t6_582jobs1




def t6_583root : Job := ⟨plan6878,[],none,⟨15,6,0⟩⟩
def t6_583jobs0 : List Job := [⟨plan6878,[],none,⟨15,6,0⟩⟩]

def t6_583jobs : List Job := t6_583jobs0




def t6_584root : Job := ⟨plan6879,[],none,⟨15,6,0⟩⟩
def t6_584jobs0 : List Job := [⟨plan5584,[⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5584,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨14,6,(-3)⟩⟩,⟨plan5584,[⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨14,6,(-4)⟩⟩]

def t6_584jobs1 : List Job := [⟨plan5584,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨13,6,(-2)⟩⟩,⟨plan5584,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨13,6,(-3)⟩⟩]

def t6_584jobs : List Job := t6_584jobs0++t6_584jobs1




def t6_585root : Job := ⟨plan6569,[],none,⟨15,3,0⟩⟩
def t6_585jobs0 : List Job := [⟨plan6569,[],none,⟨15,3,0⟩⟩]

def t6_585jobs : List Job := t6_585jobs0




def t6_586root : Job := ⟨plan6880,[],none,⟨15,6,0⟩⟩
def t6_586jobs0 : List Job := [⟨plan6880,[],none,⟨15,6,0⟩⟩]

def t6_586jobs : List Job := t6_586jobs0




def t6_587root : Job := ⟨plan6881,[],none,⟨15,6,0⟩⟩
def t6_587jobs0 : List Job := [⟨plan6881,[],none,⟨15,6,0⟩⟩]

def t6_587jobs : List Job := t6_587jobs0




def t6_588root : Job := ⟨plan6882,[],none,⟨15,6,0⟩⟩
def t6_588jobs0 : List Job := [⟨plan6882,[],none,⟨15,6,0⟩⟩]

def t6_588jobs : List Job := t6_588jobs0




def t6_589root : Job := ⟨plan6883,[],none,⟨15,6,0⟩⟩
def t6_589jobs0 : List Job := [⟨plan5588,[⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5588,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨14,6,(-3)⟩⟩,⟨plan5588,[⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨14,6,(-4)⟩⟩]

def t6_589jobs1 : List Job := [⟨plan5588,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨13,6,(-2)⟩⟩,⟨plan5588,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨13,6,(-3)⟩⟩]

def t6_589jobs : List Job := t6_589jobs0++t6_589jobs1




def t6_590root : Job := ⟨plan6884,[],none,⟨15,6,0⟩⟩
def t6_590jobs0 : List Job := [⟨plan6884,[],none,⟨15,6,0⟩⟩]

def t6_590jobs : List Job := t6_590jobs0




def t6_591root : Job := ⟨plan6885,[],none,⟨15,6,0⟩⟩
def t6_591jobs0 : List Job := [⟨plan6885,[],none,⟨15,6,0⟩⟩]

def t6_591jobs : List Job := t6_591jobs0




def t6_592root : Job := ⟨plan6886,[],none,⟨15,6,0⟩⟩
def t6_592jobs0 : List Job := [⟨plan6886,[],none,⟨15,6,0⟩⟩]

def t6_592jobs : List Job := t6_592jobs0




def t6_593root : Job := ⟨plan6887,[],none,⟨15,6,0⟩⟩
def t6_593jobs0 : List Job := [⟨plan6887,[],none,⟨15,6,0⟩⟩]

def t6_593jobs : List Job := t6_593jobs0




def t6_594root : Job := ⟨plan6888,[],none,⟨15,6,0⟩⟩
def t6_594jobs0 : List Job := [⟨plan6888,[],none,⟨15,6,0⟩⟩]

def t6_594jobs : List Job := t6_594jobs0




def t6_595root : Job := ⟨plan6889,[],none,⟨15,6,0⟩⟩
def t6_595jobs0 : List Job := [⟨plan5594,[⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5594,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨14,6,(-3)⟩⟩,⟨plan5594,[⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨14,6,(-4)⟩⟩]

def t6_595jobs1 : List Job := [⟨plan5594,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨13,6,(-2)⟩⟩,⟨plan5594,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨13,6,(-3)⟩⟩]

def t6_595jobs : List Job := t6_595jobs0++t6_595jobs1



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


