-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks059
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks059
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:25:18.244322+00:00
-- url     : https://prove2.me/theorems/5c7bd562-1595-463f-8950-f3569cdb3959
-- title:
--   Endpoint22 Reach Checks059 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks059 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_434jobs`, `ThreeBoundEndpoint22Reachable.t6_435root`, `ThreeBoundEndpoint22Reachable.t6_435jobs0`, `ThreeBoundEndpoint22Reachable.t6_435jobs`, `ThreeBoundEndpoint22Reachable.t6_436root`, `ThreeBoundEndpoint22Reachable.t6_436jobs0`, `ThreeBoundEndpoint22Reachable.t6_436jobs`, `ThreeBoundEndpoint22Reachable.t6_437root`, `ThreeBoundEndpoint22Reachable.t6_437jobs0`, `ThreeBoundEndpoint22Reachable.t6_437jobs`, `ThreeBoundEndpoint22Reachable.t6_438root`, `ThreeBoundEndpoint22Reachable.t6_438jobs0`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks059.lean, lines 1–528.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans065
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans066
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans067
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans068
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans071
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans075
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

def t6_423root : Job := ⟨plan7271,[],none,⟨15,10,0⟩⟩
def t6_423jobs0 : List Job := [⟨plan3507,[⟨1,0,5⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3507,[⟨1,0,5⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3507,[⟨1,0,5⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3507,[⟨1,0,5⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨13,8,(-5)⟩⟩,⟨plan3507,[⟨1,0,5⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3507,[⟨1,0,5⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨12,9,(-3)⟩⟩,⟨plan3507,[⟨1,0,5⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨12,8,(-4)⟩⟩,⟨plan3507,[⟨1,1,4⟩,⟨6,0,4⟩],(some ⟨6,0,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3507,[⟨1,1,4⟩,⟨6,1,3⟩],(some ⟨6,1,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3507,[⟨1,1,4⟩,⟨6,1,4⟩],(some ⟨6,1,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3507,[⟨1,1,4⟩,⟨6,2,2⟩],(some ⟨6,2,2⟩),⟨12,8,(-4)⟩⟩,⟨plan3507,[⟨1,1,4⟩,⟨6,2,3⟩],(some ⟨6,2,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3507,[⟨1,1,4⟩,⟨6,3,1⟩],(some ⟨6,3,1⟩),⟨11,9,(-2)⟩⟩]

def t6_423jobs1 : List Job := [⟨plan3507,[⟨1,1,4⟩,⟨6,3,2⟩],(some ⟨6,3,2⟩),⟨11,8,(-3)⟩⟩]

def t6_423jobs : List Job := t6_423jobs0++t6_423jobs1




def t6_424root : Job := ⟨plan7272,[],none,⟨15,10,0⟩⟩
def t6_424jobs0 : List Job := [⟨plan7272,[],none,⟨15,10,0⟩⟩]

def t6_424jobs : List Job := t6_424jobs0




def t6_425root : Job := ⟨plan7273,[],none,⟨15,10,0⟩⟩
def t6_425jobs0 : List Job := [⟨plan7273,[],none,⟨15,10,0⟩⟩]

def t6_425jobs : List Job := t6_425jobs0




def t6_426root : Job := ⟨plan7274,[],none,⟨15,10,0⟩⟩
def t6_426jobs0 : List Job := [⟨plan7274,[],none,⟨15,10,0⟩⟩]

def t6_426jobs : List Job := t6_426jobs0




def t6_427root : Job := ⟨plan7275,[],none,⟨15,10,0⟩⟩
def t6_427jobs0 : List Job := [⟨plan7275,[],none,⟨15,10,0⟩⟩]

def t6_427jobs : List Job := t6_427jobs0




def t6_428root : Job := ⟨plan6525,[],none,⟨15,3,0⟩⟩
def t6_428jobs0 : List Job := [⟨plan6525,[],none,⟨15,3,0⟩⟩]

def t6_428jobs : List Job := t6_428jobs0




def t6_429root : Job := ⟨plan6846,[],none,⟨15,6,0⟩⟩
def t6_429jobs0 : List Job := [⟨plan6846,[],none,⟨15,6,0⟩⟩]

def t6_429jobs : List Job := t6_429jobs0




def t6_430root : Job := ⟨plan6847,[],none,⟨15,6,0⟩⟩
def t6_430jobs0 : List Job := [⟨plan6847,[],none,⟨15,6,0⟩⟩]

def t6_430jobs : List Job := t6_430jobs0




def t6_431root : Job := ⟨plan6848,[],none,⟨15,6,0⟩⟩
def t6_431jobs0 : List Job := [⟨plan6848,[],none,⟨15,6,0⟩⟩]

def t6_431jobs : List Job := t6_431jobs0




def t6_432root : Job := ⟨plan6359,[],none,⟨15,1,0⟩⟩
def t6_432jobs0 : List Job := [⟨plan6359,[],none,⟨15,1,0⟩⟩]

def t6_432jobs : List Job := t6_432jobs0




def t6_433root : Job := ⟨plan6526,[],none,⟨15,3,0⟩⟩
def t6_433jobs0 : List Job := [⟨plan6526,[],none,⟨15,3,0⟩⟩]

def t6_433jobs : List Job := t6_433jobs0




def t6_434root : Job := ⟨plan6527,[],none,⟨15,3,0⟩⟩
def t6_434jobs0 : List Job := [⟨plan6527,[],none,⟨15,3,0⟩⟩]

def t6_434jobs : List Job := t6_434jobs0




def t6_435root : Job := ⟨plan6528,[],none,⟨15,3,0⟩⟩
def t6_435jobs0 : List Job := [⟨plan6528,[],none,⟨15,3,0⟩⟩]

def t6_435jobs : List Job := t6_435jobs0




def t6_436root : Job := ⟨plan6849,[],none,⟨15,6,0⟩⟩
def t6_436jobs0 : List Job := [⟨plan6849,[],none,⟨15,6,0⟩⟩]

def t6_436jobs : List Job := t6_436jobs0




def t6_437root : Job := ⟨plan6850,[],none,⟨15,6,0⟩⟩
def t6_437jobs0 : List Job := [⟨plan6850,[],none,⟨15,6,0⟩⟩]

def t6_437jobs : List Job := t6_437jobs0




def t6_438root : Job := ⟨plan6851,[],none,⟨15,6,0⟩⟩
def t6_438jobs0 : List Job := [⟨plan6851,[],none,⟨15,6,0⟩⟩]

def t6_438jobs : List Job := t6_438jobs0




def t6_439root : Job := ⟨plan6852,[],none,⟨15,6,0⟩⟩
def t6_439jobs0 : List Job := [⟨plan6852,[],none,⟨15,6,0⟩⟩]

def t6_439jobs : List Job := t6_439jobs0




def t6_440root : Job := ⟨plan6853,[],none,⟨15,6,0⟩⟩
def t6_440jobs0 : List Job := [⟨plan6853,[],none,⟨15,6,0⟩⟩]

def t6_440jobs : List Job := t6_440jobs0




def t6_441root : Job := ⟨plan6854,[],none,⟨15,6,0⟩⟩
def t6_441jobs0 : List Job := [⟨plan6854,[],none,⟨15,6,0⟩⟩]

def t6_441jobs : List Job := t6_441jobs0




def t6_442root : Job := ⟨plan6855,[],none,⟨15,6,0⟩⟩
def t6_442jobs0 : List Job := [⟨plan6855,[],none,⟨15,6,0⟩⟩]

def t6_442jobs : List Job := t6_442jobs0




def t6_443root : Job := ⟨plan7276,[],none,⟨15,10,0⟩⟩
def t6_443jobs0 : List Job := [⟨plan7276,[],none,⟨15,10,0⟩⟩]

def t6_443jobs : List Job := t6_443jobs0




def t6_444root : Job := ⟨plan7277,[],none,⟨15,10,0⟩⟩
def t6_444jobs0 : List Job := [⟨plan7277,[],none,⟨15,10,0⟩⟩]

def t6_444jobs : List Job := t6_444jobs0




def t6_445root : Job := ⟨plan7278,[],none,⟨15,10,0⟩⟩
def t6_445jobs0 : List Job := [⟨plan7278,[],none,⟨15,10,0⟩⟩]

def t6_445jobs : List Job := t6_445jobs0




def t6_446root : Job := ⟨plan7279,[],none,⟨15,10,0⟩⟩
def t6_446jobs0 : List Job := [⟨plan7279,[],none,⟨15,10,0⟩⟩]

def t6_446jobs : List Job := t6_446jobs0




def t6_447root : Job := ⟨plan7280,[],none,⟨15,10,0⟩⟩
def t6_447jobs0 : List Job := [⟨plan7280,[],none,⟨15,10,0⟩⟩]

def t6_447jobs : List Job := t6_447jobs0




def t6_448root : Job := ⟨plan7281,[],none,⟨15,10,0⟩⟩
def t6_448jobs0 : List Job := [⟨plan7281,[],none,⟨15,10,0⟩⟩]

def t6_448jobs : List Job := t6_448jobs0




def t6_449root : Job := ⟨plan7282,[],none,⟨15,10,0⟩⟩
def t6_449jobs0 : List Job := [⟨plan7282,[],none,⟨15,10,0⟩⟩]

def t6_449jobs : List Job := t6_449jobs0




def t6_450root : Job := ⟨plan7283,[],none,⟨15,10,0⟩⟩
def t6_450jobs0 : List Job := [⟨plan7283,[],none,⟨15,10,0⟩⟩]

def t6_450jobs : List Job := t6_450jobs0




def t6_451root : Job := ⟨plan7284,[],none,⟨15,10,0⟩⟩
def t6_451jobs0 : List Job := [⟨plan7284,[],none,⟨15,10,0⟩⟩]

def t6_451jobs : List Job := t6_451jobs0




def t6_452root : Job := ⟨plan7285,[],none,⟨15,10,0⟩⟩
def t6_452jobs0 : List Job := [⟨plan7285,[],none,⟨15,10,0⟩⟩]

def t6_452jobs : List Job := t6_452jobs0




def t6_453root : Job := ⟨plan7286,[],none,⟨15,10,0⟩⟩
def t6_453jobs0 : List Job := [⟨plan7286,[],none,⟨15,10,0⟩⟩]

def t6_453jobs : List Job := t6_453jobs0




def t6_454root : Job := ⟨plan6856,[],none,⟨15,6,0⟩⟩
def t6_454jobs0 : List Job := [⟨plan6856,[],none,⟨15,6,0⟩⟩]

def t6_454jobs : List Job := t6_454jobs0




def t6_455root : Job := ⟨plan7287,[],none,⟨15,10,0⟩⟩
def t6_455jobs0 : List Job := [⟨plan7287,[],none,⟨15,10,0⟩⟩]

def t6_455jobs : List Job := t6_455jobs0




def t6_456root : Job := ⟨plan7288,[],none,⟨15,10,0⟩⟩
def t6_456jobs0 : List Job := [⟨plan7288,[],none,⟨15,10,0⟩⟩]

def t6_456jobs : List Job := t6_456jobs0




def t6_457root : Job := ⟨plan7289,[],none,⟨15,10,0⟩⟩
def t6_457jobs0 : List Job := [⟨plan7289,[],none,⟨15,10,0⟩⟩]

def t6_457jobs : List Job := t6_457jobs0




def t6_458root : Job := ⟨plan7290,[],none,⟨15,10,0⟩⟩
def t6_458jobs0 : List Job := [⟨plan7290,[],none,⟨15,10,0⟩⟩]

def t6_458jobs : List Job := t6_458jobs0




def t6_459root : Job := ⟨plan7291,[],none,⟨15,10,0⟩⟩
def t6_459jobs0 : List Job := [⟨plan7291,[],none,⟨15,10,0⟩⟩]

def t6_459jobs : List Job := t6_459jobs0




def t6_460root : Job := ⟨plan7292,[],none,⟨15,10,0⟩⟩
def t6_460jobs0 : List Job := [⟨plan7292,[],none,⟨15,10,0⟩⟩]

def t6_460jobs : List Job := t6_460jobs0




def t6_461root : Job := ⟨plan6296,[],none,⟨15,0,0⟩⟩
def t6_461jobs0 : List Job := [⟨plan6296,[],none,⟨15,0,0⟩⟩]

def t6_461jobs : List Job := t6_461jobs0




def t6_462root : Job := ⟨plan6360,[],none,⟨15,1,0⟩⟩
def t6_462jobs0 : List Job := [⟨plan6360,[],none,⟨15,1,0⟩⟩]

def t6_462jobs : List Job := t6_462jobs0




def t6_463root : Job := ⟨plan6361,[],none,⟨15,1,0⟩⟩
def t6_463jobs0 : List Job := [⟨plan6361,[],none,⟨15,1,0⟩⟩]

def t6_463jobs : List Job := t6_463jobs0




def t6_464root : Job := ⟨plan6362,[],none,⟨15,1,0⟩⟩
def t6_464jobs0 : List Job := [⟨plan6362,[],none,⟨15,1,0⟩⟩]

def t6_464jobs : List Job := t6_464jobs0




def t6_465root : Job := ⟨plan6529,[],none,⟨15,3,0⟩⟩
def t6_465jobs0 : List Job := [⟨plan6529,[],none,⟨15,3,0⟩⟩]

def t6_465jobs : List Job := t6_465jobs0




def t6_466root : Job := ⟨plan6530,[],none,⟨15,3,0⟩⟩
def t6_466jobs0 : List Job := [⟨plan5527,[⟨1,0,3⟩],(some ⟨1,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5527,[⟨1,1,2⟩],(some ⟨1,1,2⟩),⟨14,3,(-2)⟩⟩]

def t6_466jobs1 : List Job := [⟨plan5527,[⟨1,1,3⟩],(some ⟨1,1,3⟩),⟨14,3,(-3)⟩⟩]

def t6_466jobs : List Job := t6_466jobs0++t6_466jobs1




def t6_467root : Job := ⟨plan6531,[],none,⟨15,3,0⟩⟩
def t6_467jobs0 : List Job := [⟨plan6531,[],none,⟨15,3,0⟩⟩]

def t6_467jobs : List Job := t6_467jobs0




def t6_468root : Job := ⟨plan6532,[],none,⟨15,3,0⟩⟩
def t6_468jobs0 : List Job := [⟨plan5529,[⟨1,0,3⟩],(some ⟨1,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5529,[⟨1,1,2⟩],(some ⟨1,1,2⟩),⟨14,3,(-2)⟩⟩]

def t6_468jobs1 : List Job := [⟨plan5529,[⟨1,1,3⟩],(some ⟨1,1,3⟩),⟨14,3,(-3)⟩⟩]

def t6_468jobs : List Job := t6_468jobs0++t6_468jobs1



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


