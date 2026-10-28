-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks013
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks013
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:28:34.22845+00:00
-- url     : https://prove2.me/theorems/7ff6ca7d-70ac-46ef-ae02-26854b3a0d41
-- title:
--   Endpoint22 Reach Checks013 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks013 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t5_580root`, `ThreeBoundEndpoint22Reachable.t5_580jobs0`, `ThreeBoundEndpoint22Reachable.t5_580jobs`, `ThreeBoundEndpoint22Reachable.t5_581root`, `ThreeBoundEndpoint22Reachable.t5_581jobs0`, `ThreeBoundEndpoint22Reachable.t5_581jobs`, `ThreeBoundEndpoint22Reachable.t5_582root`, `ThreeBoundEndpoint22Reachable.t5_582jobs0`, `ThreeBoundEndpoint22Reachable.t5_582jobs`, `ThreeBoundEndpoint22Reachable.t5_583root`, `ThreeBoundEndpoint22Reachable.t5_583jobs0`, `ThreeBoundEndpoint22Reachable.t5_583jobs`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks013.lean, lines 1–582.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans038
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans040
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans043
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans044
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans048
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

def t5_567root : Job := ⟨plan4211,[],none,⟨10,3,0⟩⟩
def t5_567jobs0 : List Job := [⟨plan4211,[],none,⟨10,3,0⟩⟩]

def t5_567jobs : List Job := t5_567jobs0




def t5_568root : Job := ⟨plan4212,[],none,⟨10,3,0⟩⟩
def t5_568jobs0 : List Job := [⟨plan4212,[],none,⟨10,3,0⟩⟩]

def t5_568jobs : List Job := t5_568jobs0




def t5_569root : Job := ⟨plan4213,[],none,⟨10,3,0⟩⟩
def t5_569jobs0 : List Job := [⟨plan4213,[],none,⟨10,3,0⟩⟩]

def t5_569jobs : List Job := t5_569jobs0




def t5_570root : Job := ⟨plan4214,[],none,⟨10,3,0⟩⟩
def t5_570jobs0 : List Job := [⟨plan4214,[],none,⟨10,3,0⟩⟩]

def t5_570jobs : List Job := t5_570jobs0




def t5_571root : Job := ⟨plan4215,[],none,⟨10,3,0⟩⟩
def t5_571jobs0 : List Job := [⟨plan4215,[],none,⟨10,3,0⟩⟩]

def t5_571jobs : List Job := t5_571jobs0




def t5_572root : Job := ⟨plan4216,[],none,⟨10,3,0⟩⟩
def t5_572jobs0 : List Job := [⟨plan4216,[],none,⟨10,3,0⟩⟩]

def t5_572jobs : List Job := t5_572jobs0




def t5_573root : Job := ⟨plan3892,[],none,⟨10,1,0⟩⟩
def t5_573jobs0 : List Job := [⟨plan3892,[],none,⟨10,1,0⟩⟩]

def t5_573jobs : List Job := t5_573jobs0




def t5_574root : Job := ⟨plan4217,[],none,⟨10,3,0⟩⟩
def t5_574jobs0 : List Job := [⟨plan4217,[],none,⟨10,3,0⟩⟩]

def t5_574jobs : List Job := t5_574jobs0




def t5_575root : Job := ⟨plan4218,[],none,⟨10,3,0⟩⟩
def t5_575jobs0 : List Job := [⟨plan4218,[],none,⟨10,3,0⟩⟩]

def t5_575jobs : List Job := t5_575jobs0




def t5_576root : Job := ⟨plan4219,[],none,⟨10,3,0⟩⟩
def t5_576jobs0 : List Job := [⟨plan4219,[],none,⟨10,3,0⟩⟩]

def t5_576jobs : List Job := t5_576jobs0




def t5_577root : Job := ⟨plan4612,[],none,⟨10,6,0⟩⟩
def t5_577jobs0 : List Job := [⟨plan4612,[],none,⟨10,6,0⟩⟩]

def t5_577jobs : List Job := t5_577jobs0




def t5_578root : Job := ⟨plan4613,[],none,⟨10,6,0⟩⟩
def t5_578jobs0 : List Job := [⟨plan4613,[],none,⟨10,6,0⟩⟩]

def t5_578jobs : List Job := t5_578jobs0




def t5_579root : Job := ⟨plan4614,[],none,⟨10,6,0⟩⟩
def t5_579jobs0 : List Job := [⟨plan4614,[],none,⟨10,6,0⟩⟩]

def t5_579jobs : List Job := t5_579jobs0




def t5_580root : Job := ⟨plan4615,[],none,⟨10,6,0⟩⟩
def t5_580jobs0 : List Job := [⟨plan4615,[],none,⟨10,6,0⟩⟩]

def t5_580jobs : List Job := t5_580jobs0




def t5_581root : Job := ⟨plan4616,[],none,⟨10,6,0⟩⟩
def t5_581jobs0 : List Job := [⟨plan4616,[],none,⟨10,6,0⟩⟩]

def t5_581jobs : List Job := t5_581jobs0




def t5_582root : Job := ⟨plan4617,[],none,⟨10,6,0⟩⟩
def t5_582jobs0 : List Job := [⟨plan4617,[],none,⟨10,6,0⟩⟩]

def t5_582jobs : List Job := t5_582jobs0




def t5_583root : Job := ⟨plan4618,[],none,⟨10,6,0⟩⟩
def t5_583jobs0 : List Job := [⟨plan4618,[],none,⟨10,6,0⟩⟩]

def t5_583jobs : List Job := t5_583jobs0




def t5_584root : Job := ⟨plan4619,[],none,⟨10,6,0⟩⟩
def t5_584jobs0 : List Job := [⟨plan4619,[],none,⟨10,6,0⟩⟩]

def t5_584jobs : List Job := t5_584jobs0




def t5_585root : Job := ⟨plan4620,[],none,⟨10,6,0⟩⟩
def t5_585jobs0 : List Job := [⟨plan4620,[],none,⟨10,6,0⟩⟩]

def t5_585jobs : List Job := t5_585jobs0




def t5_586root : Job := ⟨plan4621,[],none,⟨10,6,0⟩⟩
def t5_586jobs0 : List Job := [⟨plan4621,[],none,⟨10,6,0⟩⟩]

def t5_586jobs : List Job := t5_586jobs0




def t5_587root : Job := ⟨plan4622,[],none,⟨10,6,0⟩⟩
def t5_587jobs0 : List Job := [⟨plan4622,[],none,⟨10,6,0⟩⟩]

def t5_587jobs : List Job := t5_587jobs0




def t5_588root : Job := ⟨plan4623,[],none,⟨10,6,0⟩⟩
def t5_588jobs0 : List Job := [⟨plan4623,[],none,⟨10,6,0⟩⟩]

def t5_588jobs : List Job := t5_588jobs0




def t5_589root : Job := ⟨plan4624,[],none,⟨10,6,0⟩⟩
def t5_589jobs0 : List Job := [⟨plan4624,[],none,⟨10,6,0⟩⟩]

def t5_589jobs : List Job := t5_589jobs0




def t5_590root : Job := ⟨plan4625,[],none,⟨10,6,0⟩⟩
def t5_590jobs0 : List Job := [⟨plan4625,[],none,⟨10,6,0⟩⟩]

def t5_590jobs : List Job := t5_590jobs0




def t5_591root : Job := ⟨plan4626,[],none,⟨10,6,0⟩⟩
def t5_591jobs0 : List Job := [⟨plan4626,[],none,⟨10,6,0⟩⟩]

def t5_591jobs : List Job := t5_591jobs0




def t5_592root : Job := ⟨plan4220,[],none,⟨10,3,0⟩⟩
def t5_592jobs0 : List Job := [⟨plan4220,[],none,⟨10,3,0⟩⟩]

def t5_592jobs : List Job := t5_592jobs0




def t5_593root : Job := ⟨plan4627,[],none,⟨10,6,0⟩⟩
def t5_593jobs0 : List Job := [⟨plan4627,[],none,⟨10,6,0⟩⟩]

def t5_593jobs : List Job := t5_593jobs0




def t5_594root : Job := ⟨plan4628,[],none,⟨10,6,0⟩⟩
def t5_594jobs0 : List Job := [⟨plan4628,[],none,⟨10,6,0⟩⟩]

def t5_594jobs : List Job := t5_594jobs0




def t5_595root : Job := ⟨plan4629,[],none,⟨10,6,0⟩⟩
def t5_595jobs0 : List Job := [⟨plan4629,[],none,⟨10,6,0⟩⟩]

def t5_595jobs : List Job := t5_595jobs0




def t5_596root : Job := ⟨plan3893,[],none,⟨10,1,0⟩⟩
def t5_596jobs0 : List Job := [⟨plan3893,[],none,⟨10,1,0⟩⟩]

def t5_596jobs : List Job := t5_596jobs0




def t5_597root : Job := ⟨plan4221,[],none,⟨10,3,0⟩⟩
def t5_597jobs0 : List Job := [⟨plan4221,[],none,⟨10,3,0⟩⟩]

def t5_597jobs : List Job := t5_597jobs0




def t5_598root : Job := ⟨plan4222,[],none,⟨10,3,0⟩⟩
def t5_598jobs0 : List Job := [⟨plan4222,[],none,⟨10,3,0⟩⟩]

def t5_598jobs : List Job := t5_598jobs0




def t5_599root : Job := ⟨plan4223,[],none,⟨10,3,0⟩⟩
def t5_599jobs0 : List Job := [⟨plan4223,[],none,⟨10,3,0⟩⟩]

def t5_599jobs : List Job := t5_599jobs0




def t5_600root : Job := ⟨plan4630,[],none,⟨10,6,0⟩⟩
def t5_600jobs0 : List Job := [⟨plan4630,[],none,⟨10,6,0⟩⟩]

def t5_600jobs : List Job := t5_600jobs0




def t5_601root : Job := ⟨plan4631,[],none,⟨10,6,0⟩⟩
def t5_601jobs0 : List Job := [⟨plan4631,[],none,⟨10,6,0⟩⟩]

def t5_601jobs : List Job := t5_601jobs0




def t5_602root : Job := ⟨plan4632,[],none,⟨10,6,0⟩⟩
def t5_602jobs0 : List Job := [⟨plan4632,[],none,⟨10,6,0⟩⟩]

def t5_602jobs : List Job := t5_602jobs0




def t5_603root : Job := ⟨plan4633,[],none,⟨10,6,0⟩⟩
def t5_603jobs0 : List Job := [⟨plan4633,[],none,⟨10,6,0⟩⟩]

def t5_603jobs : List Job := t5_603jobs0




def t5_604root : Job := ⟨plan4634,[],none,⟨10,6,0⟩⟩
def t5_604jobs0 : List Job := [⟨plan4634,[],none,⟨10,6,0⟩⟩]

def t5_604jobs : List Job := t5_604jobs0




def t5_605root : Job := ⟨plan4635,[],none,⟨10,6,0⟩⟩
def t5_605jobs0 : List Job := [⟨plan4635,[],none,⟨10,6,0⟩⟩]

def t5_605jobs : List Job := t5_605jobs0




def t5_606root : Job := ⟨plan4636,[],none,⟨10,6,0⟩⟩
def t5_606jobs0 : List Job := [⟨plan4636,[],none,⟨10,6,0⟩⟩]

def t5_606jobs : List Job := t5_606jobs0




def t5_607root : Job := ⟨plan4637,[],none,⟨10,6,0⟩⟩
def t5_607jobs0 : List Job := [⟨plan4637,[],none,⟨10,6,0⟩⟩]

def t5_607jobs : List Job := t5_607jobs0




def t5_608root : Job := ⟨plan4638,[],none,⟨10,6,0⟩⟩
def t5_608jobs0 : List Job := [⟨plan4638,[],none,⟨10,6,0⟩⟩]

def t5_608jobs : List Job := t5_608jobs0




def t5_609root : Job := ⟨plan4639,[],none,⟨10,6,0⟩⟩
def t5_609jobs0 : List Job := [⟨plan4639,[],none,⟨10,6,0⟩⟩]

def t5_609jobs : List Job := t5_609jobs0




def t5_610root : Job := ⟨plan3725,[],none,⟨10,0,0⟩⟩
def t5_610jobs0 : List Job := [⟨plan3725,[],none,⟨10,0,0⟩⟩]

def t5_610jobs : List Job := t5_610jobs0




def t5_611root : Job := ⟨plan3894,[],none,⟨10,1,0⟩⟩
def t5_611jobs0 : List Job := [⟨plan3894,[],none,⟨10,1,0⟩⟩]

def t5_611jobs : List Job := t5_611jobs0




def t5_612root : Job := ⟨plan3895,[],none,⟨10,1,0⟩⟩
def t5_612jobs0 : List Job := [⟨plan3895,[],none,⟨10,1,0⟩⟩]

def t5_612jobs : List Job := t5_612jobs0




def t5_613root : Job := ⟨plan3896,[],none,⟨10,1,0⟩⟩
def t5_613jobs0 : List Job := [⟨plan3896,[],none,⟨10,1,0⟩⟩]

def t5_613jobs : List Job := t5_613jobs0




def t5_614root : Job := ⟨plan4224,[],none,⟨10,3,0⟩⟩
def t5_614jobs0 : List Job := [⟨plan4224,[],none,⟨10,3,0⟩⟩]

def t5_614jobs : List Job := t5_614jobs0




def t5_615root : Job := ⟨plan4225,[],none,⟨10,3,0⟩⟩
def t5_615jobs0 : List Job := [⟨plan2863,[⟨1,0,3⟩],(some ⟨1,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2863,[⟨1,1,2⟩],(some ⟨1,1,2⟩),⟨9,3,(-2)⟩⟩]

def t5_615jobs1 : List Job := [⟨plan2863,[⟨1,1,3⟩],(some ⟨1,1,3⟩),⟨9,3,(-3)⟩⟩]

def t5_615jobs : List Job := t5_615jobs0++t5_615jobs1




def t5_616root : Job := ⟨plan4226,[],none,⟨10,3,0⟩⟩
def t5_616jobs0 : List Job := [⟨plan2864,[⟨1,0,3⟩],(some ⟨1,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2864,[⟨1,1,2⟩],(some ⟨1,1,2⟩),⟨9,3,(-2)⟩⟩]

def t5_616jobs1 : List Job := [⟨plan2864,[⟨1,1,3⟩],(some ⟨1,1,3⟩),⟨9,3,(-3)⟩⟩]

def t5_616jobs : List Job := t5_616jobs0++t5_616jobs1




def t5_617root : Job := ⟨plan4227,[],none,⟨10,3,0⟩⟩
def t5_617jobs0 : List Job := [⟨plan2865,[⟨1,0,3⟩],(some ⟨1,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2865,[⟨1,1,2⟩],(some ⟨1,1,2⟩),⟨9,3,(-2)⟩⟩]

def t5_617jobs1 : List Job := [⟨plan2865,[⟨1,1,3⟩],(some ⟨1,1,3⟩),⟨9,3,(-3)⟩⟩]

def t5_617jobs : List Job := t5_617jobs0++t5_617jobs1



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


