-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks012
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks012
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:26:06.51698+00:00
-- url     : https://prove2.me/theorems/5e6833a1-f1d0-497b-b1dd-9d912c74759a
-- title:
--   Endpoint22 Reach Checks012 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks012 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t5_530root`, `ThreeBoundEndpoint22Reachable.t5_530jobs0`, `ThreeBoundEndpoint22Reachable.t5_530jobs`, `ThreeBoundEndpoint22Reachable.t5_531root`, `ThreeBoundEndpoint22Reachable.t5_531jobs0`, `ThreeBoundEndpoint22Reachable.t5_531jobs`, `ThreeBoundEndpoint22Reachable.t5_532root`, `ThreeBoundEndpoint22Reachable.t5_532jobs0`, `ThreeBoundEndpoint22Reachable.t5_532jobs`, `ThreeBoundEndpoint22Reachable.t5_533root`, `ThreeBoundEndpoint22Reachable.t5_533jobs0`, `ThreeBoundEndpoint22Reachable.t5_533jobs`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks012.lean, lines 1–567.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans038
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans040
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans043
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans047
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

def t5_517root : Job := ⟨plan4584,[],none,⟨10,6,0⟩⟩
def t5_517jobs0 : List Job := [⟨plan4584,[],none,⟨10,6,0⟩⟩]

def t5_517jobs : List Job := t5_517jobs0




def t5_518root : Job := ⟨plan4585,[],none,⟨10,6,0⟩⟩
def t5_518jobs0 : List Job := [⟨plan4585,[],none,⟨10,6,0⟩⟩]

def t5_518jobs : List Job := t5_518jobs0




def t5_519root : Job := ⟨plan4586,[],none,⟨10,6,0⟩⟩
def t5_519jobs0 : List Job := [⟨plan4586,[],none,⟨10,6,0⟩⟩]

def t5_519jobs : List Job := t5_519jobs0




def t5_520root : Job := ⟨plan4587,[],none,⟨10,6,0⟩⟩
def t5_520jobs0 : List Job := [⟨plan4587,[],none,⟨10,6,0⟩⟩]

def t5_520jobs : List Job := t5_520jobs0




def t5_521root : Job := ⟨plan4588,[],none,⟨10,6,0⟩⟩
def t5_521jobs0 : List Job := [⟨plan4588,[],none,⟨10,6,0⟩⟩]

def t5_521jobs : List Job := t5_521jobs0




def t5_522root : Job := ⟨plan3884,[],none,⟨10,1,0⟩⟩
def t5_522jobs0 : List Job := [⟨plan3884,[],none,⟨10,1,0⟩⟩]

def t5_522jobs : List Job := t5_522jobs0




def t5_523root : Job := ⟨plan4199,[],none,⟨10,3,0⟩⟩
def t5_523jobs0 : List Job := [⟨plan4199,[],none,⟨10,3,0⟩⟩]

def t5_523jobs : List Job := t5_523jobs0




def t5_524root : Job := ⟨plan4200,[],none,⟨10,3,0⟩⟩
def t5_524jobs0 : List Job := [⟨plan2826,[⟨1,0,3⟩],(some ⟨1,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2826,[⟨1,1,2⟩],(some ⟨1,1,2⟩),⟨9,3,(-2)⟩⟩]

def t5_524jobs1 : List Job := [⟨plan2826,[⟨1,1,3⟩],(some ⟨1,1,3⟩),⟨9,3,(-3)⟩⟩]

def t5_524jobs : List Job := t5_524jobs0++t5_524jobs1




def t5_525root : Job := ⟨plan4201,[],none,⟨10,3,0⟩⟩
def t5_525jobs0 : List Job := [⟨plan4201,[],none,⟨10,3,0⟩⟩]

def t5_525jobs : List Job := t5_525jobs0




def t5_526root : Job := ⟨plan4589,[],none,⟨10,6,0⟩⟩
def t5_526jobs0 : List Job := [⟨plan4589,[],none,⟨10,6,0⟩⟩]

def t5_526jobs : List Job := t5_526jobs0




def t5_527root : Job := ⟨plan4590,[],none,⟨10,6,0⟩⟩
def t5_527jobs0 : List Job := [⟨plan4590,[],none,⟨10,6,0⟩⟩]

def t5_527jobs : List Job := t5_527jobs0




def t5_528root : Job := ⟨plan4591,[],none,⟨10,6,0⟩⟩
def t5_528jobs0 : List Job := [⟨plan4591,[],none,⟨10,6,0⟩⟩]

def t5_528jobs : List Job := t5_528jobs0




def t5_529root : Job := ⟨plan4592,[],none,⟨10,6,0⟩⟩
def t5_529jobs0 : List Job := [⟨plan4592,[],none,⟨10,6,0⟩⟩]

def t5_529jobs : List Job := t5_529jobs0




def t5_530root : Job := ⟨plan4202,[],none,⟨10,3,0⟩⟩
def t5_530jobs0 : List Job := [⟨plan4202,[],none,⟨10,3,0⟩⟩]

def t5_530jobs : List Job := t5_530jobs0




def t5_531root : Job := ⟨plan4593,[],none,⟨10,6,0⟩⟩
def t5_531jobs0 : List Job := [⟨plan4593,[],none,⟨10,6,0⟩⟩]

def t5_531jobs : List Job := t5_531jobs0




def t5_532root : Job := ⟨plan4594,[],none,⟨10,6,0⟩⟩
def t5_532jobs0 : List Job := [⟨plan4594,[],none,⟨10,6,0⟩⟩]

def t5_532jobs : List Job := t5_532jobs0




def t5_533root : Job := ⟨plan4595,[],none,⟨10,6,0⟩⟩
def t5_533jobs0 : List Job := [⟨plan4595,[],none,⟨10,6,0⟩⟩]

def t5_533jobs : List Job := t5_533jobs0




def t5_534root : Job := ⟨plan4596,[],none,⟨10,6,0⟩⟩
def t5_534jobs0 : List Job := [⟨plan4596,[],none,⟨10,6,0⟩⟩]

def t5_534jobs : List Job := t5_534jobs0




def t5_535root : Job := ⟨plan4597,[],none,⟨10,6,0⟩⟩
def t5_535jobs0 : List Job := [⟨plan4597,[],none,⟨10,6,0⟩⟩]

def t5_535jobs : List Job := t5_535jobs0




def t5_536root : Job := ⟨plan4598,[],none,⟨10,6,0⟩⟩
def t5_536jobs0 : List Job := [⟨plan4598,[],none,⟨10,6,0⟩⟩]

def t5_536jobs : List Job := t5_536jobs0




def t5_537root : Job := ⟨plan4599,[],none,⟨10,6,0⟩⟩
def t5_537jobs0 : List Job := [⟨plan4599,[],none,⟨10,6,0⟩⟩]

def t5_537jobs : List Job := t5_537jobs0




def t5_538root : Job := ⟨plan4600,[],none,⟨10,6,0⟩⟩
def t5_538jobs0 : List Job := [⟨plan4600,[],none,⟨10,6,0⟩⟩]

def t5_538jobs : List Job := t5_538jobs0




def t5_539root : Job := ⟨plan4601,[],none,⟨10,6,0⟩⟩
def t5_539jobs0 : List Job := [⟨plan4601,[],none,⟨10,6,0⟩⟩]

def t5_539jobs : List Job := t5_539jobs0




def t5_540root : Job := ⟨plan4602,[],none,⟨10,6,0⟩⟩
def t5_540jobs0 : List Job := [⟨plan4602,[],none,⟨10,6,0⟩⟩]

def t5_540jobs : List Job := t5_540jobs0




def t5_541root : Job := ⟨plan4603,[],none,⟨10,6,0⟩⟩
def t5_541jobs0 : List Job := [⟨plan4603,[],none,⟨10,6,0⟩⟩]

def t5_541jobs : List Job := t5_541jobs0




def t5_542root : Job := ⟨plan4604,[],none,⟨10,6,0⟩⟩
def t5_542jobs0 : List Job := [⟨plan4604,[],none,⟨10,6,0⟩⟩]

def t5_542jobs : List Job := t5_542jobs0




def t5_543root : Job := ⟨plan4605,[],none,⟨10,6,0⟩⟩
def t5_543jobs0 : List Job := [⟨plan4605,[],none,⟨10,6,0⟩⟩]

def t5_543jobs : List Job := t5_543jobs0




def t5_544root : Job := ⟨plan4606,[],none,⟨10,6,0⟩⟩
def t5_544jobs0 : List Job := [⟨plan4606,[],none,⟨10,6,0⟩⟩]

def t5_544jobs : List Job := t5_544jobs0




def t5_545root : Job := ⟨plan4607,[],none,⟨10,6,0⟩⟩
def t5_545jobs0 : List Job := [⟨plan4607,[],none,⟨10,6,0⟩⟩]

def t5_545jobs : List Job := t5_545jobs0




def t5_546root : Job := ⟨plan4608,[],none,⟨10,6,0⟩⟩
def t5_546jobs0 : List Job := [⟨plan4608,[],none,⟨10,6,0⟩⟩]

def t5_546jobs : List Job := t5_546jobs0




def t5_547root : Job := ⟨plan4609,[],none,⟨10,6,0⟩⟩
def t5_547jobs0 : List Job := [⟨plan4609,[],none,⟨10,6,0⟩⟩]

def t5_547jobs : List Job := t5_547jobs0




def t5_548root : Job := ⟨plan4610,[],none,⟨10,6,0⟩⟩
def t5_548jobs0 : List Job := [⟨plan4610,[],none,⟨10,6,0⟩⟩]

def t5_548jobs : List Job := t5_548jobs0




def t5_549root : Job := ⟨plan4611,[],none,⟨10,6,0⟩⟩
def t5_549jobs0 : List Job := [⟨plan4611,[],none,⟨10,6,0⟩⟩]

def t5_549jobs : List Job := t5_549jobs0




def t5_550root : Job := ⟨plan3885,[],none,⟨10,1,0⟩⟩
def t5_550jobs0 : List Job := [⟨plan3885,[],none,⟨10,1,0⟩⟩]

def t5_550jobs : List Job := t5_550jobs0




def t5_551root : Job := ⟨plan3723,[],none,⟨10,0,0⟩⟩
def t5_551jobs0 : List Job := [⟨plan3723,[],none,⟨10,0,0⟩⟩]

def t5_551jobs : List Job := t5_551jobs0




def t5_552root : Job := ⟨plan3886,[],none,⟨10,1,0⟩⟩
def t5_552jobs0 : List Job := [⟨plan3886,[],none,⟨10,1,0⟩⟩]

def t5_552jobs : List Job := t5_552jobs0




def t5_553root : Job := ⟨plan3887,[],none,⟨10,1,0⟩⟩
def t5_553jobs0 : List Job := [⟨plan3887,[],none,⟨10,1,0⟩⟩]

def t5_553jobs : List Job := t5_553jobs0




def t5_554root : Job := ⟨plan3888,[],none,⟨10,1,0⟩⟩
def t5_554jobs0 : List Job := [⟨plan3888,[],none,⟨10,1,0⟩⟩]

def t5_554jobs : List Job := t5_554jobs0




def t5_555root : Job := ⟨plan4203,[],none,⟨10,3,0⟩⟩
def t5_555jobs0 : List Job := [⟨plan4203,[],none,⟨10,3,0⟩⟩]

def t5_555jobs : List Job := t5_555jobs0




def t5_556root : Job := ⟨plan4204,[],none,⟨10,3,0⟩⟩
def t5_556jobs0 : List Job := [⟨plan4204,[],none,⟨10,3,0⟩⟩]

def t5_556jobs : List Job := t5_556jobs0




def t5_557root : Job := ⟨plan4205,[],none,⟨10,3,0⟩⟩
def t5_557jobs0 : List Job := [⟨plan4205,[],none,⟨10,3,0⟩⟩]

def t5_557jobs : List Job := t5_557jobs0




def t5_558root : Job := ⟨plan4206,[],none,⟨10,3,0⟩⟩
def t5_558jobs0 : List Job := [⟨plan4206,[],none,⟨10,3,0⟩⟩]

def t5_558jobs : List Job := t5_558jobs0




def t5_559root : Job := ⟨plan4207,[],none,⟨10,3,0⟩⟩
def t5_559jobs0 : List Job := [⟨plan4207,[],none,⟨10,3,0⟩⟩]

def t5_559jobs : List Job := t5_559jobs0




def t5_560root : Job := ⟨plan4208,[],none,⟨10,3,0⟩⟩
def t5_560jobs0 : List Job := [⟨plan4208,[],none,⟨10,3,0⟩⟩]

def t5_560jobs : List Job := t5_560jobs0




def t5_561root : Job := ⟨plan4209,[],none,⟨10,3,0⟩⟩
def t5_561jobs0 : List Job := [⟨plan4209,[],none,⟨10,3,0⟩⟩]

def t5_561jobs : List Job := t5_561jobs0




def t5_562root : Job := ⟨plan4210,[],none,⟨10,3,0⟩⟩
def t5_562jobs0 : List Job := [⟨plan4210,[],none,⟨10,3,0⟩⟩]

def t5_562jobs : List Job := t5_562jobs0




def t5_563root : Job := ⟨plan3724,[],none,⟨10,0,0⟩⟩
def t5_563jobs0 : List Job := [⟨plan3724,[],none,⟨10,0,0⟩⟩]

def t5_563jobs : List Job := t5_563jobs0




def t5_564root : Job := ⟨plan3889,[],none,⟨10,1,0⟩⟩
def t5_564jobs0 : List Job := [⟨plan3889,[],none,⟨10,1,0⟩⟩]

def t5_564jobs : List Job := t5_564jobs0




def t5_565root : Job := ⟨plan3890,[],none,⟨10,1,0⟩⟩
def t5_565jobs0 : List Job := [⟨plan3890,[],none,⟨10,1,0⟩⟩]

def t5_565jobs : List Job := t5_565jobs0




def t5_566root : Job := ⟨plan3891,[],none,⟨10,1,0⟩⟩
def t5_566jobs0 : List Job := [⟨plan3891,[],none,⟨10,1,0⟩⟩]

def t5_566jobs : List Job := t5_566jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


