-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks118
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks118
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:29:34.062811+00:00
-- url     : https://prove2.me/theorems/761ce723-0f8d-4b5e-9861-26bf34c8c3de
-- title:
--   Endpoint22 Reach Checks118 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks118 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_965root`, `ThreeBoundEndpoint22Reachable.t6_965jobs0`, `ThreeBoundEndpoint22Reachable.t6_965jobs1`, `ThreeBoundEndpoint22Reachable.t6_965jobs2`, `ThreeBoundEndpoint22Reachable.t6_965jobs`, `ThreeBoundEndpoint22Reachable.t6_966root`, `ThreeBoundEndpoint22Reachable.t6_966jobs0`, `ThreeBoundEndpoint22Reachable.t6_966jobs`, `ThreeBoundEndpoint22Reachable.t6_967root`, `ThreeBoundEndpoint22Reachable.t6_967jobs0`, `ThreeBoundEndpoint22Reachable.t6_967jobs1`, `ThreeBoundEndpoint22Reachable.t6_967jobs2`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks118.lean, lines 1–260.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans065
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans066
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans069
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans073
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans077
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

def t6_952root : Job := ⟨plan7456,[],none,⟨15,10,0⟩⟩
def t6_952jobs0 : List Job := [⟨plan7456,[],none,⟨15,10,0⟩⟩]

def t6_952jobs : List Job := t6_952jobs0




def t6_953root : Job := ⟨plan7457,[],none,⟨15,10,0⟩⟩
def t6_953jobs0 : List Job := [⟨plan7457,[],none,⟨15,10,0⟩⟩]

def t6_953jobs : List Job := t6_953jobs0




def t6_954root : Job := ⟨plan7458,[],none,⟨15,10,0⟩⟩
def t6_954jobs0 : List Job := [⟨plan7458,[],none,⟨15,10,0⟩⟩]

def t6_954jobs : List Job := t6_954jobs0




def t6_955root : Job := ⟨plan7459,[],none,⟨15,10,0⟩⟩
def t6_955jobs0 : List Job := [⟨plan7459,[],none,⟨15,10,0⟩⟩]

def t6_955jobs : List Job := t6_955jobs0




def t6_956root : Job := ⟨plan7460,[],none,⟨15,10,0⟩⟩
def t6_956jobs0 : List Job := [⟨plan7460,[],none,⟨15,10,0⟩⟩]

def t6_956jobs : List Job := t6_956jobs0




def t6_957root : Job := ⟨plan7461,[],none,⟨15,10,0⟩⟩
def t6_957jobs0 : List Job := [⟨plan7461,[],none,⟨15,10,0⟩⟩]

def t6_957jobs : List Job := t6_957jobs0




def t6_958root : Job := ⟨plan7462,[],none,⟨15,10,0⟩⟩
def t6_958jobs0 : List Job := [⟨plan7462,[],none,⟨15,10,0⟩⟩]

def t6_958jobs : List Job := t6_958jobs0




def t6_959root : Job := ⟨plan7463,[],none,⟨15,10,0⟩⟩
def t6_959jobs0 : List Job := [⟨plan7463,[],none,⟨15,10,0⟩⟩]

def t6_959jobs : List Job := t6_959jobs0




def t6_960root : Job := ⟨plan6315,[],none,⟨15,0,0⟩⟩
def t6_960jobs0 : List Job := [⟨plan6315,[],none,⟨15,0,0⟩⟩]

def t6_960jobs : List Job := t6_960jobs0




def t6_961root : Job := ⟨plan6411,[],none,⟨15,1,0⟩⟩
def t6_961jobs0 : List Job := [⟨plan6411,[],none,⟨15,1,0⟩⟩]

def t6_961jobs : List Job := t6_961jobs0




def t6_962root : Job := ⟨plan6412,[],none,⟨15,1,0⟩⟩
def t6_962jobs0 : List Job := [⟨plan6412,[],none,⟨15,1,0⟩⟩]

def t6_962jobs : List Job := t6_962jobs0




def t6_963root : Job := ⟨plan6413,[],none,⟨15,1,0⟩⟩
def t6_963jobs0 : List Job := [⟨plan6413,[],none,⟨15,1,0⟩⟩]

def t6_963jobs : List Job := t6_963jobs0




def t6_964root : Job := ⟨plan6630,[],none,⟨15,3,0⟩⟩
def t6_964jobs0 : List Job := [⟨plan6630,[],none,⟨15,3,0⟩⟩]

def t6_964jobs : List Job := t6_964jobs0




def t6_965root : Job := ⟨plan6631,[],none,⟨15,3,0⟩⟩
def t6_965jobs0 : List Job := [⟨plan5481,[⟨4,0,2⟩],(some ⟨4,0,2⟩),⟨15,1,(-2)⟩⟩]

def t6_965jobs1 : List Job := [⟨plan5481,[⟨4,1,1⟩],(some ⟨4,1,1⟩),⟨14,2,0⟩⟩]

def t6_965jobs2 : List Job := [⟨plan5481,[⟨4,1,2⟩],(some ⟨4,1,2⟩),⟨14,1,(-1)⟩⟩]

def t6_965jobs : List Job := t6_965jobs0++t6_965jobs1++t6_965jobs2




def t6_966root : Job := ⟨plan6632,[],none,⟨15,3,0⟩⟩
def t6_966jobs0 : List Job := [⟨plan6632,[],none,⟨15,3,0⟩⟩]

def t6_966jobs : List Job := t6_966jobs0




def t6_967root : Job := ⟨plan6633,[],none,⟨15,3,0⟩⟩
def t6_967jobs0 : List Job := [⟨plan5483,[⟨4,0,2⟩],(some ⟨4,0,2⟩),⟨15,1,(-2)⟩⟩]

def t6_967jobs1 : List Job := [⟨plan5483,[⟨4,1,1⟩],(some ⟨4,1,1⟩),⟨14,2,0⟩⟩]

def t6_967jobs2 : List Job := [⟨plan5483,[⟨4,1,2⟩],(some ⟨4,1,2⟩),⟨14,1,(-1)⟩⟩]

def t6_967jobs : List Job := t6_967jobs0++t6_967jobs1++t6_967jobs2




def t6_968root : Job := ⟨plan6634,[],none,⟨15,3,0⟩⟩
def t6_968jobs0 : List Job := [⟨plan5484,[⟨4,0,2⟩],(some ⟨4,0,2⟩),⟨15,1,(-2)⟩⟩]

def t6_968jobs1 : List Job := [⟨plan5484,[⟨4,1,1⟩],(some ⟨4,1,1⟩),⟨14,2,0⟩⟩]

def t6_968jobs2 : List Job := [⟨plan5484,[⟨4,1,2⟩],(some ⟨4,1,2⟩),⟨14,1,(-1)⟩⟩]

def t6_968jobs : List Job := t6_968jobs0++t6_968jobs1++t6_968jobs2




def t6_969root : Job := ⟨plan6635,[],none,⟨15,3,0⟩⟩
def t6_969jobs0 : List Job := [⟨plan6635,[],none,⟨15,3,0⟩⟩]

def t6_969jobs : List Job := t6_969jobs0




def t6_970root : Job := ⟨plan7010,[],none,⟨15,6,0⟩⟩
def t6_970jobs0 : List Job := [⟨plan7010,[],none,⟨15,6,0⟩⟩]

def t6_970jobs : List Job := t6_970jobs0




def t6_971root : Job := ⟨plan7011,[],none,⟨15,6,0⟩⟩
def t6_971jobs0 : List Job := [⟨plan5623,[⟨4,0,3⟩],(some ⟨4,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5623,[⟨4,1,2⟩],(some ⟨4,1,2⟩),⟨14,4,(-1)⟩⟩]

def t6_971jobs1 : List Job := [⟨plan5623,[⟨4,1,3⟩],(some ⟨4,1,3⟩),⟨14,3,(-2)⟩⟩]

def t6_971jobs : List Job := t6_971jobs0++t6_971jobs1




def t6_972root : Job := ⟨plan7012,[],none,⟨15,6,0⟩⟩
def t6_972jobs0 : List Job := [⟨plan7012,[],none,⟨15,6,0⟩⟩]

def t6_972jobs : List Job := t6_972jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


