-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks189
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks189
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:34:14.156106+00:00
-- url     : https://prove2.me/theorems/473b0d45-07a4-4f13-bbdc-18f811478553
-- title:
--   Endpoint22 Reach Checks189 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks189 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t7_573root`, `ThreeBoundEndpoint22Reachable.t7_573jobs0`, `ThreeBoundEndpoint22Reachable.t7_573jobs`, `ThreeBoundEndpoint22Reachable.t7_574root`, `ThreeBoundEndpoint22Reachable.t7_574jobs0`, `ThreeBoundEndpoint22Reachable.t7_574jobs`, `ThreeBoundEndpoint22Reachable.t7_575root`, `ThreeBoundEndpoint22Reachable.t7_575jobs0`, `ThreeBoundEndpoint22Reachable.t7_575jobs`, `ThreeBoundEndpoint22Reachable.t7_576root`, `ThreeBoundEndpoint22Reachable.t7_576jobs0`, `ThreeBoundEndpoint22Reachable.t7_576jobs`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks189.lean, lines 1–817.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans088
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans090
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans092
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans094
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

def t7_560root : Job := ⟨plan8684,[],none,⟨21,10,0⟩⟩
def t7_560jobs0 : List Job := [⟨plan8684,[],none,⟨21,10,0⟩⟩]

def t7_560jobs : List Job := t7_560jobs0




def t7_561root : Job := ⟨plan8685,[],none,⟨21,10,0⟩⟩
def t7_561jobs0 : List Job := [⟨plan8685,[],none,⟨21,10,0⟩⟩]

def t7_561jobs : List Job := t7_561jobs0




def t7_562root : Job := ⟨plan8686,[],none,⟨21,10,0⟩⟩
def t7_562jobs0 : List Job := [⟨plan8686,[],none,⟨21,10,0⟩⟩]

def t7_562jobs : List Job := t7_562jobs0




def t7_563root : Job := ⟨plan8896,[],none,⟨21,15,0⟩⟩
def t7_563jobs0 : List Job := [⟨plan8896,[],none,⟨21,15,0⟩⟩]

def t7_563jobs : List Job := t7_563jobs0




def t7_564root : Job := ⟨plan8897,[],none,⟨21,15,0⟩⟩
def t7_564jobs0 : List Job := [⟨plan8897,[],none,⟨21,15,0⟩⟩]

def t7_564jobs : List Job := t7_564jobs0




def t7_565root : Job := ⟨plan8898,[],none,⟨21,15,0⟩⟩
def t7_565jobs0 : List Job := [⟨plan8898,[],none,⟨21,15,0⟩⟩]

def t7_565jobs : List Job := t7_565jobs0




def t7_566root : Job := ⟨plan8899,[],none,⟨21,15,0⟩⟩
def t7_566jobs0 : List Job := [⟨plan8899,[],none,⟨21,15,0⟩⟩]

def t7_566jobs : List Job := t7_566jobs0




def t7_567root : Job := ⟨plan8900,[],none,⟨21,15,0⟩⟩
def t7_567jobs0 : List Job := [⟨plan8900,[],none,⟨21,15,0⟩⟩]

def t7_567jobs : List Job := t7_567jobs0




def t7_568root : Job := ⟨plan8901,[],none,⟨21,15,0⟩⟩
def t7_568jobs0 : List Job := [⟨plan8901,[],none,⟨21,15,0⟩⟩]

def t7_568jobs : List Job := t7_568jobs0




def t7_569root : Job := ⟨plan8902,[],none,⟨21,15,0⟩⟩
def t7_569jobs0 : List Job := [⟨plan8902,[],none,⟨21,15,0⟩⟩]

def t7_569jobs : List Job := t7_569jobs0




def t7_570root : Job := ⟨plan8903,[],none,⟨21,15,0⟩⟩
def t7_570jobs0 : List Job := [⟨plan8903,[],none,⟨21,15,0⟩⟩]

def t7_570jobs : List Job := t7_570jobs0




def t7_571root : Job := ⟨plan8461,[],none,⟨21,3,0⟩⟩
def t7_571jobs0 : List Job := [⟨plan8461,[],none,⟨21,3,0⟩⟩]

def t7_571jobs : List Job := t7_571jobs0




def t7_572root : Job := ⟨plan8537,[],none,⟨21,6,0⟩⟩
def t7_572jobs0 : List Job := [⟨plan8537,[],none,⟨21,6,0⟩⟩]

def t7_572jobs : List Job := t7_572jobs0




def t7_573root : Job := ⟨plan8538,[],none,⟨21,6,0⟩⟩
def t7_573jobs0 : List Job := [⟨plan8538,[],none,⟨21,6,0⟩⟩]

def t7_573jobs : List Job := t7_573jobs0




def t7_574root : Job := ⟨plan8539,[],none,⟨21,6,0⟩⟩
def t7_574jobs0 : List Job := [⟨plan8539,[],none,⟨21,6,0⟩⟩]

def t7_574jobs : List Job := t7_574jobs0




def t7_575root : Job := ⟨plan8687,[],none,⟨21,10,0⟩⟩
def t7_575jobs0 : List Job := [⟨plan8687,[],none,⟨21,10,0⟩⟩]

def t7_575jobs : List Job := t7_575jobs0




def t7_576root : Job := ⟨plan8688,[],none,⟨21,10,0⟩⟩
def t7_576jobs0 : List Job := [⟨plan8688,[],none,⟨21,10,0⟩⟩]

def t7_576jobs : List Job := t7_576jobs0




def t7_577root : Job := ⟨plan8689,[],none,⟨21,10,0⟩⟩
def t7_577jobs0 : List Job := [⟨plan8689,[],none,⟨21,10,0⟩⟩]

def t7_577jobs : List Job := t7_577jobs0




def t7_578root : Job := ⟨plan8690,[],none,⟨21,10,0⟩⟩
def t7_578jobs0 : List Job := [⟨plan8690,[],none,⟨21,10,0⟩⟩]

def t7_578jobs : List Job := t7_578jobs0




def t7_579root : Job := ⟨plan8691,[],none,⟨21,10,0⟩⟩
def t7_579jobs0 : List Job := [⟨plan8691,[],none,⟨21,10,0⟩⟩]

def t7_579jobs : List Job := t7_579jobs0




def t7_580root : Job := ⟨plan8692,[],none,⟨21,10,0⟩⟩
def t7_580jobs0 : List Job := [⟨plan8692,[],none,⟨21,10,0⟩⟩]

def t7_580jobs : List Job := t7_580jobs0




def t7_581root : Job := ⟨plan8904,[],none,⟨21,15,0⟩⟩
def t7_581jobs0 : List Job := [⟨plan8904,[],none,⟨21,15,0⟩⟩]

def t7_581jobs : List Job := t7_581jobs0




def t7_582root : Job := ⟨plan8905,[],none,⟨21,15,0⟩⟩
def t7_582jobs0 : List Job := [⟨plan8905,[],none,⟨21,15,0⟩⟩]

def t7_582jobs : List Job := t7_582jobs0




def t7_583root : Job := ⟨plan8906,[],none,⟨21,15,0⟩⟩
def t7_583jobs0 : List Job := [⟨plan8906,[],none,⟨21,15,0⟩⟩]

def t7_583jobs : List Job := t7_583jobs0




def t7_584root : Job := ⟨plan8907,[],none,⟨21,15,0⟩⟩
def t7_584jobs0 : List Job := [⟨plan8907,[],none,⟨21,15,0⟩⟩]

def t7_584jobs : List Job := t7_584jobs0




def t7_585root : Job := ⟨plan8908,[],none,⟨21,15,0⟩⟩
def t7_585jobs0 : List Job := [⟨plan8908,[],none,⟨21,15,0⟩⟩]

def t7_585jobs : List Job := t7_585jobs0




def t7_586root : Job := ⟨plan8909,[],none,⟨21,15,0⟩⟩
def t7_586jobs0 : List Job := [⟨plan8909,[],none,⟨21,15,0⟩⟩]

def t7_586jobs : List Job := t7_586jobs0




def t7_587root : Job := ⟨plan8910,[],none,⟨21,15,0⟩⟩
def t7_587jobs0 : List Job := [⟨plan8910,[],none,⟨21,15,0⟩⟩]

def t7_587jobs : List Job := t7_587jobs0




def t7_588root : Job := ⟨plan8911,[],none,⟨21,15,0⟩⟩
def t7_588jobs0 : List Job := [⟨plan8911,[],none,⟨21,15,0⟩⟩]

def t7_588jobs : List Job := t7_588jobs0




def t7_589root : Job := ⟨plan8912,[],none,⟨21,15,0⟩⟩
def t7_589jobs0 : List Job := [⟨plan8912,[],none,⟨21,15,0⟩⟩]

def t7_589jobs : List Job := t7_589jobs0




def t7_590root : Job := ⟨plan8913,[],none,⟨21,15,0⟩⟩
def t7_590jobs0 : List Job := [⟨plan8913,[],none,⟨21,15,0⟩⟩]

def t7_590jobs : List Job := t7_590jobs0




def t7_591root : Job := ⟨plan8693,[],none,⟨21,10,0⟩⟩
def t7_591jobs0 : List Job := [⟨plan8693,[],none,⟨21,10,0⟩⟩]

def t7_591jobs : List Job := t7_591jobs0




def t7_592root : Job := ⟨plan8914,[],none,⟨21,15,0⟩⟩
def t7_592jobs0 : List Job := [⟨plan8914,[],none,⟨21,15,0⟩⟩]

def t7_592jobs : List Job := t7_592jobs0




def t7_593root : Job := ⟨plan8915,[],none,⟨21,15,0⟩⟩
def t7_593jobs0 : List Job := [⟨plan8915,[],none,⟨21,15,0⟩⟩]

def t7_593jobs : List Job := t7_593jobs0




def t7_594root : Job := ⟨plan8916,[],none,⟨21,15,0⟩⟩
def t7_594jobs0 : List Job := [⟨plan8916,[],none,⟨21,15,0⟩⟩]

def t7_594jobs : List Job := t7_594jobs0




def t7_595root : Job := ⟨plan9058,[],none,⟨21,21,0⟩⟩
def t7_595jobs0 : List Job := [⟨plan9058,[],none,⟨21,21,0⟩⟩]

def t7_595jobs : List Job := t7_595jobs0




def t7_596root : Job := ⟨plan9059,[],none,⟨21,21,0⟩⟩
def t7_596jobs0 : List Job := [⟨plan9059,[],none,⟨21,21,0⟩⟩]

def t7_596jobs : List Job := t7_596jobs0




def t7_597root : Job := ⟨plan9060,[],none,⟨21,21,0⟩⟩
def t7_597jobs0 : List Job := [⟨plan9060,[],none,⟨21,21,0⟩⟩]

def t7_597jobs : List Job := t7_597jobs0




def t7_598root : Job := ⟨plan9061,[],none,⟨21,21,0⟩⟩
def t7_598jobs0 : List Job := [⟨plan9061,[],none,⟨21,21,0⟩⟩]

def t7_598jobs : List Job := t7_598jobs0




def t7_599root : Job := ⟨plan9062,[],none,⟨21,21,0⟩⟩
def t7_599jobs0 : List Job := [⟨plan9062,[],none,⟨21,21,0⟩⟩]

def t7_599jobs : List Job := t7_599jobs0




def t7_600root : Job := ⟨plan9063,[],none,⟨21,21,0⟩⟩
def t7_600jobs0 : List Job := [⟨plan9063,[],none,⟨21,21,0⟩⟩]

def t7_600jobs : List Job := t7_600jobs0




def t7_601root : Job := ⟨plan9064,[],none,⟨21,21,0⟩⟩
def t7_601jobs0 : List Job := [⟨plan9064,[],none,⟨21,21,0⟩⟩]

def t7_601jobs : List Job := t7_601jobs0




def t7_602root : Job := ⟨plan9065,[],none,⟨21,21,0⟩⟩
def t7_602jobs0 : List Job := [⟨plan9065,[],none,⟨21,21,0⟩⟩]

def t7_602jobs : List Job := t7_602jobs0




def t7_603root : Job := ⟨plan9066,[],none,⟨21,21,0⟩⟩
def t7_603jobs0 : List Job := [⟨plan9066,[],none,⟨21,21,0⟩⟩]

def t7_603jobs : List Job := t7_603jobs0




def t7_604root : Job := ⟨plan9067,[],none,⟨21,21,0⟩⟩
def t7_604jobs0 : List Job := [⟨plan9067,[],none,⟨21,21,0⟩⟩]

def t7_604jobs : List Job := t7_604jobs0




def t7_605root : Job := ⟨plan9068,[],none,⟨21,21,0⟩⟩
def t7_605jobs0 : List Job := [⟨plan9068,[],none,⟨21,21,0⟩⟩]

def t7_605jobs : List Job := t7_605jobs0




def t7_606root : Job := ⟨plan9069,[],none,⟨21,21,0⟩⟩
def t7_606jobs0 : List Job := [⟨plan9069,[],none,⟨21,21,0⟩⟩]

def t7_606jobs : List Job := t7_606jobs0




def t7_607root : Job := ⟨plan9070,[],none,⟨21,21,0⟩⟩
def t7_607jobs0 : List Job := [⟨plan9070,[],none,⟨21,21,0⟩⟩]

def t7_607jobs : List Job := t7_607jobs0




def t7_608root : Job := ⟨plan9071,[],none,⟨21,21,0⟩⟩
def t7_608jobs0 : List Job := [⟨plan9071,[],none,⟨21,21,0⟩⟩]

def t7_608jobs : List Job := t7_608jobs0




def t7_609root : Job := ⟨plan9072,[],none,⟨21,21,0⟩⟩
def t7_609jobs0 : List Job := [⟨plan9072,[],none,⟨21,21,0⟩⟩]

def t7_609jobs : List Job := t7_609jobs0




def t7_610root : Job := ⟨plan9073,[],none,⟨21,21,0⟩⟩
def t7_610jobs0 : List Job := [⟨plan9073,[],none,⟨21,21,0⟩⟩]

def t7_610jobs : List Job := t7_610jobs0




def t7_611root : Job := ⟨plan9074,[],none,⟨21,21,0⟩⟩
def t7_611jobs0 : List Job := [⟨plan9074,[],none,⟨21,21,0⟩⟩]

def t7_611jobs : List Job := t7_611jobs0




def t7_612root : Job := ⟨plan9075,[],none,⟨21,21,0⟩⟩
def t7_612jobs0 : List Job := [⟨plan9075,[],none,⟨21,21,0⟩⟩]

def t7_612jobs : List Job := t7_612jobs0




def t7_613root : Job := ⟨plan9076,[],none,⟨21,21,0⟩⟩
def t7_613jobs0 : List Job := [⟨plan9076,[],none,⟨21,21,0⟩⟩]

def t7_613jobs : List Job := t7_613jobs0




def t7_614root : Job := ⟨plan8917,[],none,⟨21,15,0⟩⟩
def t7_614jobs0 : List Job := [⟨plan8917,[],none,⟨21,15,0⟩⟩]

def t7_614jobs : List Job := t7_614jobs0




def t7_615root : Job := ⟨plan9077,[],none,⟨21,21,0⟩⟩
def t7_615jobs0 : List Job := [⟨plan9077,[],none,⟨21,21,0⟩⟩]

def t7_615jobs : List Job := t7_615jobs0




def t7_616root : Job := ⟨plan9078,[],none,⟨21,21,0⟩⟩
def t7_616jobs0 : List Job := [⟨plan9078,[],none,⟨21,21,0⟩⟩]

def t7_616jobs : List Job := t7_616jobs0




def t7_617root : Job := ⟨plan9079,[],none,⟨21,21,0⟩⟩
def t7_617jobs0 : List Job := [⟨plan9079,[],none,⟨21,21,0⟩⟩]

def t7_617jobs : List Job := t7_617jobs0




def t7_618root : Job := ⟨plan8694,[],none,⟨21,10,0⟩⟩
def t7_618jobs0 : List Job := [⟨plan8694,[],none,⟨21,10,0⟩⟩]

def t7_618jobs : List Job := t7_618jobs0




def t7_619root : Job := ⟨plan8918,[],none,⟨21,15,0⟩⟩
def t7_619jobs0 : List Job := [⟨plan8918,[],none,⟨21,15,0⟩⟩]

def t7_619jobs : List Job := t7_619jobs0




def t7_620root : Job := ⟨plan8919,[],none,⟨21,15,0⟩⟩
def t7_620jobs0 : List Job := [⟨plan8919,[],none,⟨21,15,0⟩⟩]

def t7_620jobs : List Job := t7_620jobs0




def t7_621root : Job := ⟨plan8920,[],none,⟨21,15,0⟩⟩
def t7_621jobs0 : List Job := [⟨plan8920,[],none,⟨21,15,0⟩⟩]

def t7_621jobs : List Job := t7_621jobs0




def t7_622root : Job := ⟨plan9080,[],none,⟨21,21,0⟩⟩
def t7_622jobs0 : List Job := [⟨plan9080,[],none,⟨21,21,0⟩⟩]

def t7_622jobs : List Job := t7_622jobs0




def t7_623root : Job := ⟨plan9081,[],none,⟨21,21,0⟩⟩
def t7_623jobs0 : List Job := [⟨plan9081,[],none,⟨21,21,0⟩⟩]

def t7_623jobs : List Job := t7_623jobs0




def t7_624root : Job := ⟨plan9082,[],none,⟨21,21,0⟩⟩
def t7_624jobs0 : List Job := [⟨plan9082,[],none,⟨21,21,0⟩⟩]

def t7_624jobs : List Job := t7_624jobs0




def t7_625root : Job := ⟨plan9083,[],none,⟨21,21,0⟩⟩
def t7_625jobs0 : List Job := [⟨plan9083,[],none,⟨21,21,0⟩⟩]

def t7_625jobs : List Job := t7_625jobs0




def t7_626root : Job := ⟨plan9084,[],none,⟨21,21,0⟩⟩
def t7_626jobs0 : List Job := [⟨plan9084,[],none,⟨21,21,0⟩⟩]

def t7_626jobs : List Job := t7_626jobs0




def t7_627root : Job := ⟨plan9085,[],none,⟨21,21,0⟩⟩
def t7_627jobs0 : List Job := [⟨plan9085,[],none,⟨21,21,0⟩⟩]

def t7_627jobs : List Job := t7_627jobs0




def t7_628root : Job := ⟨plan9086,[],none,⟨21,21,0⟩⟩
def t7_628jobs0 : List Job := [⟨plan9086,[],none,⟨21,21,0⟩⟩]

def t7_628jobs : List Job := t7_628jobs0




def t7_629root : Job := ⟨plan9087,[],none,⟨21,21,0⟩⟩
def t7_629jobs0 : List Job := [⟨plan9087,[],none,⟨21,21,0⟩⟩]

def t7_629jobs : List Job := t7_629jobs0




def t7_630root : Job := ⟨plan9088,[],none,⟨21,21,0⟩⟩
def t7_630jobs0 : List Job := [⟨plan9088,[],none,⟨21,21,0⟩⟩]

def t7_630jobs : List Job := t7_630jobs0




def t7_631root : Job := ⟨plan9089,[],none,⟨21,21,0⟩⟩
def t7_631jobs0 : List Job := [⟨plan9089,[],none,⟨21,21,0⟩⟩]

def t7_631jobs : List Job := t7_631jobs0




def t7_632root : Job := ⟨plan9090,[],none,⟨21,21,0⟩⟩
def t7_632jobs0 : List Job := [⟨plan9090,[],none,⟨21,21,0⟩⟩]

def t7_632jobs : List Job := t7_632jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


