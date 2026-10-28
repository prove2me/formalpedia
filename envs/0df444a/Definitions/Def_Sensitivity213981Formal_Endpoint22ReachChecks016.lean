-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks016
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks016
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:24:36.89249+00:00
-- url     : https://prove2.me/theorems/591e212f-0295-4fbe-b2fd-9cad44ed8a12
-- title:
--   Endpoint22 Reach Checks016 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks016 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t5_714root`, `ThreeBoundEndpoint22Reachable.t5_714jobs0`, `ThreeBoundEndpoint22Reachable.t5_714jobs`, `ThreeBoundEndpoint22Reachable.t5_715root`, `ThreeBoundEndpoint22Reachable.t5_715jobs0`, `ThreeBoundEndpoint22Reachable.t5_715jobs`, `ThreeBoundEndpoint22Reachable.t5_716root`, `ThreeBoundEndpoint22Reachable.t5_716jobs0`, `ThreeBoundEndpoint22Reachable.t5_702root`, `ThreeBoundEndpoint22Reachable.t5_716jobs1`, `ThreeBoundEndpoint22Reachable.t5_716jobs`, `ThreeBoundEndpoint22Reachable.t5_702jobs0`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks016.lean, lines 1–314.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans038
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans040
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans044
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

def t5_701root : Job := ⟨plan4243,[],none,⟨10,3,0⟩⟩
def t5_701jobs0 : List Job := [⟨plan4243,[],none,⟨10,3,0⟩⟩]

def t5_701jobs : List Job := t5_701jobs0




def t5_702root : Job := ⟨plan4244,[],none,⟨10,3,0⟩⟩
def t5_702jobs0 : List Job := [⟨plan4244,[],none,⟨10,3,0⟩⟩]

def t5_702jobs : List Job := t5_702jobs0




def t5_703root : Job := ⟨plan4245,[],none,⟨10,3,0⟩⟩
def t5_703jobs0 : List Job := [⟨plan4245,[],none,⟨10,3,0⟩⟩]

def t5_703jobs : List Job := t5_703jobs0




def t5_704root : Job := ⟨plan4246,[],none,⟨10,3,0⟩⟩
def t5_704jobs0 : List Job := [⟨plan4246,[],none,⟨10,3,0⟩⟩]

def t5_704jobs : List Job := t5_704jobs0




def t5_705root : Job := ⟨plan4247,[],none,⟨10,3,0⟩⟩
def t5_705jobs0 : List Job := [⟨plan4247,[],none,⟨10,3,0⟩⟩]

def t5_705jobs : List Job := t5_705jobs0




def t5_706root : Job := ⟨plan4248,[],none,⟨10,3,0⟩⟩
def t5_706jobs0 : List Job := [⟨plan4248,[],none,⟨10,3,0⟩⟩]

def t5_706jobs : List Job := t5_706jobs0




def t5_707root : Job := ⟨plan4249,[],none,⟨10,3,0⟩⟩
def t5_707jobs0 : List Job := [⟨plan4249,[],none,⟨10,3,0⟩⟩]

def t5_707jobs : List Job := t5_707jobs0




def t5_708root : Job := ⟨plan4250,[],none,⟨10,3,0⟩⟩
def t5_708jobs0 : List Job := [⟨plan4250,[],none,⟨10,3,0⟩⟩]

def t5_708jobs : List Job := t5_708jobs0




def t5_709root : Job := ⟨plan4251,[],none,⟨10,3,0⟩⟩
def t5_709jobs0 : List Job := [⟨plan4251,[],none,⟨10,3,0⟩⟩]

def t5_709jobs : List Job := t5_709jobs0




def t5_710root : Job := ⟨plan4252,[],none,⟨10,3,0⟩⟩
def t5_710jobs0 : List Job := [⟨plan4252,[],none,⟨10,3,0⟩⟩]

def t5_710jobs : List Job := t5_710jobs0




def t5_711root : Job := ⟨plan4253,[],none,⟨10,3,0⟩⟩
def t5_711jobs0 : List Job := [⟨plan2742,[⟨2,0,3⟩],(some ⟨2,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2742,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨9,3,(-2)⟩⟩]

def t5_711jobs1 : List Job := [⟨plan2742,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨9,3,(-3)⟩⟩,⟨plan2742,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨8,3,(-1)⟩⟩,⟨plan2742,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,3,(-2)⟩⟩]

def t5_711jobs : List Job := t5_711jobs0++t5_711jobs1




def t5_712root : Job := ⟨plan4254,[],none,⟨10,3,0⟩⟩
def t5_712jobs0 : List Job := [⟨plan4254,[],none,⟨10,3,0⟩⟩]

def t5_712jobs : List Job := t5_712jobs0




def t5_713root : Job := ⟨plan4255,[],none,⟨10,3,0⟩⟩
def t5_713jobs0 : List Job := [⟨plan4255,[],none,⟨10,3,0⟩⟩]

def t5_713jobs : List Job := t5_713jobs0




def t5_714root : Job := ⟨plan3740,[],none,⟨10,0,0⟩⟩
def t5_714jobs0 : List Job := [⟨plan3740,[],none,⟨10,0,0⟩⟩]

def t5_714jobs : List Job := t5_714jobs0




def t5_715root : Job := ⟨plan3924,[],none,⟨10,1,0⟩⟩
def t5_715jobs0 : List Job := [⟨plan3924,[],none,⟨10,1,0⟩⟩]

def t5_715jobs : List Job := t5_715jobs0




def t5_716root : Job := ⟨plan3925,[],none,⟨10,1,0⟩⟩
def t5_716jobs0 : List Job := [⟨plan2624,[⟨2,0,2⟩],(some ⟨2,0,2⟩),⟨10,1,(-2)⟩⟩,⟨plan2624,[⟨2,1,1⟩],(some ⟨2,1,1⟩),⟨9,1,(-1)⟩⟩,⟨plan2624,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨9,1,(-2)⟩⟩]

def t5_716jobs1 : List Job := [⟨plan2624,[⟨2,2,0⟩],(some ⟨2,2,0⟩),⟨8,1,0⟩⟩,⟨plan2624,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨8,1,(-1)⟩⟩,⟨plan2624,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,1,(-2)⟩⟩]

def t5_716jobs : List Job := t5_716jobs0++t5_716jobs1




def t5_717root : Job := ⟨plan3926,[],none,⟨10,1,0⟩⟩
def t5_717jobs0 : List Job := [⟨plan3926,[],none,⟨10,1,0⟩⟩]

def t5_717jobs : List Job := t5_717jobs0




def t5_718root : Job := ⟨plan4256,[],none,⟨10,3,0⟩⟩
def t5_718jobs0 : List Job := [⟨plan4256,[],none,⟨10,3,0⟩⟩]

def t5_718jobs : List Job := t5_718jobs0




def t5_719root : Job := ⟨plan4257,[],none,⟨10,3,0⟩⟩
def t5_719jobs0 : List Job := [⟨plan4257,[],none,⟨10,3,0⟩⟩]

def t5_719jobs : List Job := t5_719jobs0




def t5_720root : Job := ⟨plan4258,[],none,⟨10,3,0⟩⟩
def t5_720jobs0 : List Job := [⟨plan4258,[],none,⟨10,3,0⟩⟩]

def t5_720jobs : List Job := t5_720jobs0




def t5_721root : Job := ⟨plan4259,[],none,⟨10,3,0⟩⟩
def t5_721jobs0 : List Job := [⟨plan4259,[],none,⟨10,3,0⟩⟩]

def t5_721jobs : List Job := t5_721jobs0




def t5_722root : Job := ⟨plan3927,[],none,⟨10,1,0⟩⟩
def t5_722jobs0 : List Job := [⟨plan3927,[],none,⟨10,1,0⟩⟩]

def t5_722jobs : List Job := t5_722jobs0




def t5_723root : Job := ⟨plan4260,[],none,⟨10,3,0⟩⟩
def t5_723jobs0 : List Job := [⟨plan4260,[],none,⟨10,3,0⟩⟩]

def t5_723jobs : List Job := t5_723jobs0




def t5_724root : Job := ⟨plan4261,[],none,⟨10,3,0⟩⟩
def t5_724jobs0 : List Job := [⟨plan4261,[],none,⟨10,3,0⟩⟩]

def t5_724jobs : List Job := t5_724jobs0




def t5_725root : Job := ⟨plan4262,[],none,⟨10,3,0⟩⟩
def t5_725jobs0 : List Job := [⟨plan4262,[],none,⟨10,3,0⟩⟩]

def t5_725jobs : List Job := t5_725jobs0




def t5_726root : Job := ⟨plan4263,[],none,⟨10,3,0⟩⟩
def t5_726jobs0 : List Job := [⟨plan4263,[],none,⟨10,3,0⟩⟩]

def t5_726jobs : List Job := t5_726jobs0




def t5_727root : Job := ⟨plan4264,[],none,⟨10,3,0⟩⟩
def t5_727jobs0 : List Job := [⟨plan4264,[],none,⟨10,3,0⟩⟩]

def t5_727jobs : List Job := t5_727jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


