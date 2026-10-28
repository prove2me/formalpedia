-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks045
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks045
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:24:35.093209+00:00
-- url     : https://prove2.me/theorems/8eb66adc-6d3d-4472-90b2-e618e5ece029
-- title:
--   Endpoint22 Reach Checks045 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks045 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t5_1615jobs2`, `ThreeBoundEndpoint22Reachable.t5_1615jobs`, `ThreeBoundEndpoint22Reachable.t5_1616root`, `ThreeBoundEndpoint22Reachable.t5_1616jobs0`, `ThreeBoundEndpoint22Reachable.t5_1616jobs1`, `ThreeBoundEndpoint22Reachable.t5_1616jobs2`, `ThreeBoundEndpoint22Reachable.t5_1616jobs`, `ThreeBoundEndpoint22Reachable.t5_1617root`, `ThreeBoundEndpoint22Reachable.t5_1617jobs0`, `ThreeBoundEndpoint22Reachable.t5_1617jobs1`, `ThreeBoundEndpoint22Reachable.t5_1617jobs2`, `ThreeBoundEndpoint22Reachable.t5_1617jobs3`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks045.lean, lines 1–124.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans046
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans051
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

def t5_1615root : Job := ⟨plan4442,[],none,⟨10,3,0⟩⟩
def t5_1615jobs0 : List Job := [⟨plan2764,[⟨9,0,2⟩],(some ⟨9,0,2⟩),⟨10,1,(-2)⟩⟩,⟨plan2764,[⟨9,1,1⟩],(some ⟨9,1,1⟩),⟨9,2,0⟩⟩,⟨plan2764,[⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨9,1,(-1)⟩⟩]

def t5_1615jobs1 : List Job := [⟨plan2764,[⟨9,2,0⟩],(some ⟨9,2,0⟩),⟨8,3,2⟩⟩,⟨plan2764,[⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨8,2,1⟩⟩]

def t5_1615jobs2 : List Job := [⟨plan2764,[⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨8,1,0⟩⟩]

def t5_1615jobs : List Job := t5_1615jobs0++t5_1615jobs1++t5_1615jobs2




def t5_1616root : Job := ⟨plan4443,[],none,⟨10,3,0⟩⟩
def t5_1616jobs0 : List Job := [⟨plan2765,[⟨9,0,2⟩],(some ⟨9,0,2⟩),⟨10,1,(-2)⟩⟩,⟨plan2765,[⟨9,1,1⟩],(some ⟨9,1,1⟩),⟨9,2,0⟩⟩,⟨plan2765,[⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨9,1,(-1)⟩⟩]

def t5_1616jobs1 : List Job := [⟨plan2765,[⟨9,2,0⟩],(some ⟨9,2,0⟩),⟨8,3,2⟩⟩,⟨plan2765,[⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨8,2,1⟩⟩]

def t5_1616jobs2 : List Job := [⟨plan2765,[⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨8,1,0⟩⟩]

def t5_1616jobs : List Job := t5_1616jobs0++t5_1616jobs1++t5_1616jobs2




def t5_1617root : Job := ⟨plan4444,[],none,⟨10,3,0⟩⟩
def t5_1617jobs0 : List Job := [⟨plan2766,[⟨9,0,2⟩],(some ⟨9,0,2⟩),⟨10,1,(-2)⟩⟩,⟨plan2766,[⟨9,1,1⟩],(some ⟨9,1,1⟩),⟨9,2,0⟩⟩]

def t5_1617jobs1 : List Job := [⟨plan2766,[⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨9,1,(-1)⟩⟩,⟨plan2766,[⟨9,2,0⟩],(some ⟨9,2,0⟩),⟨8,3,2⟩⟩]

def t5_1617jobs2 : List Job := [⟨plan2766,[⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨8,2,1⟩⟩]

def t5_1617jobs3 : List Job := [⟨plan2766,[⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨8,1,0⟩⟩]

def t5_1617jobs : List Job := t5_1617jobs0++t5_1617jobs1++t5_1617jobs2++t5_1617jobs3




def t5_1618root : Job := ⟨plan4445,[],none,⟨10,3,0⟩⟩
def t5_1618jobs0 : List Job := [⟨plan2767,[⟨9,0,2⟩],(some ⟨9,0,2⟩),⟨10,1,(-2)⟩⟩,⟨plan2767,[⟨9,1,1⟩],(some ⟨9,1,1⟩),⟨9,2,0⟩⟩,⟨plan2767,[⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨9,1,(-1)⟩⟩,⟨plan2767,[⟨9,2,0⟩],(some ⟨9,2,0⟩),⟨8,3,2⟩⟩]

def t5_1618jobs1 : List Job := [⟨plan2767,[⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨8,2,1⟩⟩,⟨plan2767,[⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨8,1,0⟩⟩]

def t5_1618jobs : List Job := t5_1618jobs0++t5_1618jobs1




def t5_1619root : Job := ⟨plan4979,[],none,⟨10,6,0⟩⟩
def t5_1619jobs0 : List Job := [⟨plan4979,[],none,⟨10,6,0⟩⟩]

def t5_1619jobs : List Job := t5_1619jobs0




def t5_1620root : Job := ⟨plan4980,[],none,⟨10,6,0⟩⟩
def t5_1620jobs0 : List Job := [⟨plan2905,[⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2905,[⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨9,4,(-1)⟩⟩,⟨plan2905,[⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨9,3,(-2)⟩⟩]

def t5_1620jobs1 : List Job := [⟨plan2905,[⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨8,5,1⟩⟩,⟨plan2905,[⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨8,4,0⟩⟩]

def t5_1620jobs : List Job := t5_1620jobs0++t5_1620jobs1




def t5_1621root : Job := ⟨plan4981,[],none,⟨10,6,0⟩⟩
def t5_1621jobs0 : List Job := [⟨plan2906,[⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2906,[⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨9,4,(-1)⟩⟩,⟨plan2906,[⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨9,3,(-2)⟩⟩,⟨plan2906,[⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨8,5,1⟩⟩]

def t5_1621jobs1 : List Job := [⟨plan2906,[⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨8,4,0⟩⟩]

def t5_1621jobs : List Job := t5_1621jobs0++t5_1621jobs1




def t5_1622root : Job := ⟨plan4982,[],none,⟨10,6,0⟩⟩
def t5_1622jobs0 : List Job := [⟨plan2907,[⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2907,[⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨9,4,(-1)⟩⟩]

def t5_1622jobs1 : List Job := [⟨plan2907,[⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨9,3,(-2)⟩⟩,⟨plan2907,[⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨8,5,1⟩⟩]

def t5_1622jobs2 : List Job := [⟨plan2907,[⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨8,4,0⟩⟩]

def t5_1622jobs : List Job := t5_1622jobs0++t5_1622jobs1++t5_1622jobs2



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


