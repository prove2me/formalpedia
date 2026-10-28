-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks052
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks052
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:27:02.796689+00:00
-- url     : https://prove2.me/theorems/9c37fc0a-9f34-4997-9fb0-70159d57f47b
-- title:
--   Endpoint22 Reach Checks052 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks052 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_281jobs`, `ThreeBoundEndpoint22Reachable.t6_293root`, `ThreeBoundEndpoint22Reachable.t6_293jobs0`, `ThreeBoundEndpoint22Reachable.t6_293jobs1`, `ThreeBoundEndpoint22Reachable.t6_293jobs`, `ThreeBoundEndpoint22Reachable.t6_294root`, `ThreeBoundEndpoint22Reachable.t6_294jobs0`, `ThreeBoundEndpoint22Reachable.t6_294jobs`, `ThreeBoundEndpoint22Reachable.t6_295root`, `ThreeBoundEndpoint22Reachable.t6_295jobs0`, `ThreeBoundEndpoint22Reachable.t6_295jobs`, `ThreeBoundEndpoint22Reachable.t6_296root`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks052.lean, lines 1–230.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans065
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans066
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans067
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans070
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

def t6_281root : Job := ⟨plan6800,[],none,⟨15,6,0⟩⟩
def t6_281jobs0 : List Job := [⟨plan5618,[⟨1,0,4⟩],(some ⟨1,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5618,[⟨1,1,3⟩],(some ⟨1,1,3⟩),⟨14,6,(-3)⟩⟩]

def t6_281jobs1 : List Job := [⟨plan5618,[⟨1,1,4⟩],(some ⟨1,1,4⟩),⟨14,6,(-4)⟩⟩]

def t6_281jobs : List Job := t6_281jobs0++t6_281jobs1




def t6_282root : Job := ⟨plan6801,[],none,⟨15,6,0⟩⟩
def t6_282jobs0 : List Job := [⟨plan5619,[⟨1,0,4⟩],(some ⟨1,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5619,[⟨1,1,3⟩],(some ⟨1,1,3⟩),⟨14,6,(-3)⟩⟩]

def t6_282jobs1 : List Job := [⟨plan5619,[⟨1,1,4⟩],(some ⟨1,1,4⟩),⟨14,6,(-4)⟩⟩]

def t6_282jobs : List Job := t6_282jobs0++t6_282jobs1




def t6_283root : Job := ⟨plan6802,[],none,⟨15,6,0⟩⟩
def t6_283jobs0 : List Job := [⟨plan6802,[],none,⟨15,6,0⟩⟩]

def t6_283jobs : List Job := t6_283jobs0




def t6_284root : Job := ⟨plan6803,[],none,⟨15,6,0⟩⟩
def t6_284jobs0 : List Job := [⟨plan6803,[],none,⟨15,6,0⟩⟩]

def t6_284jobs : List Job := t6_284jobs0




def t6_285root : Job := ⟨plan6278,[],none,⟨15,0,0⟩⟩
def t6_285jobs0 : List Job := [⟨plan6278,[],none,⟨15,0,0⟩⟩]

def t6_285jobs : List Job := t6_285jobs0




def t6_286root : Job := ⟨plan6292,[],none,⟨15,0,0⟩⟩
def t6_286jobs0 : List Job := [⟨plan6292,[],none,⟨15,0,0⟩⟩]

def t6_286jobs : List Job := t6_286jobs0




def t6_287root : Job := ⟨plan6293,[],none,⟨15,0,0⟩⟩
def t6_287jobs0 : List Job := [⟨plan6293,[],none,⟨15,0,0⟩⟩]

def t6_287jobs : List Job := t6_287jobs0




def t6_288root : Job := ⟨plan6294,[],none,⟨15,0,0⟩⟩
def t6_288jobs0 : List Job := [⟨plan6294,[],none,⟨15,0,0⟩⟩]

def t6_288jobs : List Job := t6_288jobs0




def t6_289root : Job := ⟨plan6349,[],none,⟨15,1,0⟩⟩
def t6_289jobs0 : List Job := [⟨plan6349,[],none,⟨15,1,0⟩⟩]

def t6_289jobs : List Job := t6_289jobs0




def t6_290root : Job := ⟨plan6350,[],none,⟨15,1,0⟩⟩
def t6_290jobs0 : List Job := [⟨plan5397,[⟨1,0,2⟩],(some ⟨1,0,2⟩),⟨15,1,(-2)⟩⟩,⟨plan5397,[⟨1,1,1⟩],(some ⟨1,1,1⟩),⟨14,1,(-1)⟩⟩]

def t6_290jobs1 : List Job := [⟨plan5397,[⟨1,1,2⟩],(some ⟨1,1,2⟩),⟨14,1,(-2)⟩⟩]

def t6_290jobs : List Job := t6_290jobs0++t6_290jobs1




def t6_291root : Job := ⟨plan6351,[],none,⟨15,1,0⟩⟩
def t6_291jobs0 : List Job := [⟨plan6351,[],none,⟨15,1,0⟩⟩]

def t6_291jobs : List Job := t6_291jobs0




def t6_292root : Job := ⟨plan6352,[],none,⟨15,1,0⟩⟩
def t6_292jobs0 : List Job := [⟨plan5399,[⟨1,0,2⟩],(some ⟨1,0,2⟩),⟨15,1,(-2)⟩⟩,⟨plan5399,[⟨1,1,1⟩],(some ⟨1,1,1⟩),⟨14,1,(-1)⟩⟩]

def t6_292jobs1 : List Job := [⟨plan5399,[⟨1,1,2⟩],(some ⟨1,1,2⟩),⟨14,1,(-2)⟩⟩]

def t6_292jobs : List Job := t6_292jobs0++t6_292jobs1




def t6_293root : Job := ⟨plan6353,[],none,⟨15,1,0⟩⟩
def t6_293jobs0 : List Job := [⟨plan5400,[⟨1,0,2⟩],(some ⟨1,0,2⟩),⟨15,1,(-2)⟩⟩,⟨plan5400,[⟨1,1,1⟩],(some ⟨1,1,1⟩),⟨14,1,(-1)⟩⟩]

def t6_293jobs1 : List Job := [⟨plan5400,[⟨1,1,2⟩],(some ⟨1,1,2⟩),⟨14,1,(-2)⟩⟩]

def t6_293jobs : List Job := t6_293jobs0++t6_293jobs1




def t6_294root : Job := ⟨plan6354,[],none,⟨15,1,0⟩⟩
def t6_294jobs0 : List Job := [⟨plan6354,[],none,⟨15,1,0⟩⟩]

def t6_294jobs : List Job := t6_294jobs0




def t6_295root : Job := ⟨plan6503,[],none,⟨15,3,0⟩⟩
def t6_295jobs0 : List Job := [⟨plan6503,[],none,⟨15,3,0⟩⟩]

def t6_295jobs : List Job := t6_295jobs0




def t6_296root : Job := ⟨plan6504,[],none,⟨15,3,0⟩⟩
def t6_296jobs0 : List Job := [⟨plan3313,[⟨1,0,3⟩,⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨15,3,(-6)⟩⟩,⟨plan3313,[⟨1,0,3⟩,⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨14,3,(-5)⟩⟩,⟨plan3313,[⟨1,0,3⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3313,[⟨1,0,3⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨13,3,(-4)⟩⟩,⟨plan3313,[⟨1,0,3⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨13,3,(-5)⟩⟩,⟨plan3313,[⟨1,0,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨13,3,(-6)⟩⟩,⟨plan3313,[⟨1,0,3⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨12,3,(-3)⟩⟩,⟨plan3313,[⟨1,0,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨12,3,(-4)⟩⟩,⟨plan3313,[⟨1,0,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨12,3,(-5)⟩⟩,⟨plan3313,[⟨1,1,2⟩,⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨14,3,(-5)⟩⟩,⟨plan3313,[⟨1,1,2⟩,⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨13,3,(-4)⟩⟩,⟨plan3313,[⟨1,1,2⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3313,[⟨1,1,2⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨12,3,(-3)⟩⟩,⟨plan3313,[⟨1,1,2⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨12,3,(-4)⟩⟩,⟨plan3313,[⟨1,1,2⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,3,(-5)⟩⟩,⟨plan3313,[⟨1,1,2⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨11,3,(-2)⟩⟩,⟨plan3313,[⟨1,1,2⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨11,3,(-3)⟩⟩,⟨plan3313,[⟨1,1,2⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,3,(-4)⟩⟩,⟨plan3313,[⟨1,1,3⟩,⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3313,[⟨1,1,3⟩,⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨13,3,(-5)⟩⟩,⟨plan3313,[⟨1,1,3⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨13,3,(-6)⟩⟩]

def t6_296jobs1 : List Job := [⟨plan3313,[⟨1,1,3⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨12,3,(-4)⟩⟩,⟨plan3313,[⟨1,1,3⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨12,3,(-5)⟩⟩,⟨plan3313,[⟨1,1,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,3,(-6)⟩⟩,⟨plan3313,[⟨1,1,3⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨11,3,(-3)⟩⟩,⟨plan3313,[⟨1,1,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨11,3,(-4)⟩⟩,⟨plan3313,[⟨1,1,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,3,(-5)⟩⟩]

def t6_296jobs : List Job := t6_296jobs0++t6_296jobs1




def t6_297root : Job := ⟨plan6505,[],none,⟨15,3,0⟩⟩
def t6_297jobs0 : List Job := [⟨plan6505,[],none,⟨15,3,0⟩⟩]

def t6_297jobs : List Job := t6_297jobs0




def t6_298root : Job := ⟨plan6506,[],none,⟨15,3,0⟩⟩
def t6_298jobs0 : List Job := [⟨plan3315,[⟨1,0,3⟩,⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨15,3,(-6)⟩⟩,⟨plan3315,[⟨1,0,3⟩,⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨14,3,(-5)⟩⟩,⟨plan3315,[⟨1,0,3⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3315,[⟨1,0,3⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨13,3,(-4)⟩⟩,⟨plan3315,[⟨1,0,3⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨13,3,(-5)⟩⟩,⟨plan3315,[⟨1,0,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨13,3,(-6)⟩⟩,⟨plan3315,[⟨1,0,3⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨12,3,(-3)⟩⟩,⟨plan3315,[⟨1,0,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨12,3,(-4)⟩⟩,⟨plan3315,[⟨1,0,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨12,3,(-5)⟩⟩,⟨plan3315,[⟨1,1,2⟩,⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨14,3,(-5)⟩⟩,⟨plan3315,[⟨1,1,2⟩,⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨13,3,(-4)⟩⟩,⟨plan3315,[⟨1,1,2⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3315,[⟨1,1,2⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨12,3,(-3)⟩⟩,⟨plan3315,[⟨1,1,2⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨12,3,(-4)⟩⟩]

def t6_298jobs1 : List Job := [⟨plan3315,[⟨1,1,2⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,3,(-5)⟩⟩,⟨plan3315,[⟨1,1,2⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨11,3,(-2)⟩⟩,⟨plan3315,[⟨1,1,2⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨11,3,(-3)⟩⟩,⟨plan3315,[⟨1,1,2⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,3,(-4)⟩⟩,⟨plan3315,[⟨1,1,3⟩,⟨3,0,3⟩],(some ⟨3,0,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3315,[⟨1,1,3⟩,⟨3,1,2⟩],(some ⟨3,1,2⟩),⟨13,3,(-5)⟩⟩,⟨plan3315,[⟨1,1,3⟩,⟨3,1,3⟩],(some ⟨3,1,3⟩),⟨13,3,(-6)⟩⟩]

def t6_298jobs2 : List Job := [⟨plan3315,[⟨1,1,3⟩,⟨3,2,1⟩],(some ⟨3,2,1⟩),⟨12,3,(-4)⟩⟩,⟨plan3315,[⟨1,1,3⟩,⟨3,2,2⟩],(some ⟨3,2,2⟩),⟨12,3,(-5)⟩⟩,⟨plan3315,[⟨1,1,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,3,(-6)⟩⟩]

def t6_298jobs3 : List Job := [⟨plan3315,[⟨1,1,3⟩,⟨3,3,0⟩],(some ⟨3,3,0⟩),⟨11,3,(-3)⟩⟩,⟨plan3315,[⟨1,1,3⟩,⟨3,3,1⟩],(some ⟨3,3,1⟩),⟨11,3,(-4)⟩⟩,⟨plan3315,[⟨1,1,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,3,(-5)⟩⟩]

def t6_298jobs : List Job := t6_298jobs0++t6_298jobs1++t6_298jobs2++t6_298jobs3



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


