-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks015
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks015
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:23:11.401993+00:00
-- url     : https://prove2.me/theorems/d00060da-3ed8-4e0e-b04b-5c31d8a0f0b6
-- title:
--   Endpoint22 Reach Checks015 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks015 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t5_688jobs0`, `ThreeBoundEndpoint22Reachable.t5_688jobs1`, `ThreeBoundEndpoint22Reachable.t5_688jobs`, `ThreeBoundEndpoint22Reachable.t5_689root`, `ThreeBoundEndpoint22Reachable.t5_689jobs0`, `ThreeBoundEndpoint22Reachable.t5_689jobs`, `ThreeBoundEndpoint22Reachable.t5_690root`, `ThreeBoundEndpoint22Reachable.t5_690jobs0`, `ThreeBoundEndpoint22Reachable.t5_690jobs`, `ThreeBoundEndpoint22Reachable.t5_679root`, `ThreeBoundEndpoint22Reachable.t5_691root`, `ThreeBoundEndpoint22Reachable.t5_691jobs0`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks015.lean, lines 1–280.

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

def t5_678root : Job := ⟨plan3737,[],none,⟨10,0,0⟩⟩
def t5_678jobs0 : List Job := [⟨plan3737,[],none,⟨10,0,0⟩⟩]

def t5_678jobs : List Job := t5_678jobs0




def t5_679root : Job := ⟨plan3738,[],none,⟨10,0,0⟩⟩
def t5_679jobs0 : List Job := [⟨plan3738,[],none,⟨10,0,0⟩⟩]

def t5_679jobs : List Job := t5_679jobs0




def t5_680root : Job := ⟨plan3913,[],none,⟨10,1,0⟩⟩
def t5_680jobs0 : List Job := [⟨plan3913,[],none,⟨10,1,0⟩⟩]

def t5_680jobs : List Job := t5_680jobs0




def t5_681root : Job := ⟨plan3914,[],none,⟨10,1,0⟩⟩
def t5_681jobs0 : List Job := [⟨plan2611,[⟨2,0,2⟩],(some ⟨2,0,2⟩),⟨10,1,(-2)⟩⟩,⟨plan2611,[⟨2,1,1⟩],(some ⟨2,1,1⟩),⟨9,1,(-1)⟩⟩]

def t5_681jobs1 : List Job := [⟨plan2611,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨9,1,(-2)⟩⟩,⟨plan2611,[⟨2,2,0⟩],(some ⟨2,2,0⟩),⟨8,1,0⟩⟩]

def t5_681jobs2 : List Job := [⟨plan2611,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨8,1,(-1)⟩⟩,⟨plan2611,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,1,(-2)⟩⟩]

def t5_681jobs : List Job := t5_681jobs0++t5_681jobs1++t5_681jobs2




def t5_682root : Job := ⟨plan3915,[],none,⟨10,1,0⟩⟩
def t5_682jobs0 : List Job := [⟨plan2612,[⟨2,0,2⟩],(some ⟨2,0,2⟩),⟨10,1,(-2)⟩⟩,⟨plan2612,[⟨2,1,1⟩],(some ⟨2,1,1⟩),⟨9,1,(-1)⟩⟩,⟨plan2612,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨9,1,(-2)⟩⟩]

def t5_682jobs1 : List Job := [⟨plan2612,[⟨2,2,0⟩],(some ⟨2,2,0⟩),⟨8,1,0⟩⟩,⟨plan2612,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨8,1,(-1)⟩⟩,⟨plan2612,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,1,(-2)⟩⟩]

def t5_682jobs : List Job := t5_682jobs0++t5_682jobs1




def t5_683root : Job := ⟨plan3916,[],none,⟨10,1,0⟩⟩
def t5_683jobs0 : List Job := [⟨plan2613,[⟨2,0,2⟩],(some ⟨2,0,2⟩),⟨10,1,(-2)⟩⟩,⟨plan2613,[⟨2,1,1⟩],(some ⟨2,1,1⟩),⟨9,1,(-1)⟩⟩,⟨plan2613,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨9,1,(-2)⟩⟩,⟨plan2613,[⟨2,2,0⟩],(some ⟨2,2,0⟩),⟨8,1,0⟩⟩]

def t5_683jobs1 : List Job := [⟨plan2613,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨8,1,(-1)⟩⟩,⟨plan2613,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,1,(-2)⟩⟩]

def t5_683jobs : List Job := t5_683jobs0++t5_683jobs1




def t5_684root : Job := ⟨plan3917,[],none,⟨10,1,0⟩⟩
def t5_684jobs0 : List Job := [⟨plan2614,[⟨2,0,2⟩],(some ⟨2,0,2⟩),⟨10,1,(-2)⟩⟩,⟨plan2614,[⟨2,1,1⟩],(some ⟨2,1,1⟩),⟨9,1,(-1)⟩⟩]

def t5_684jobs1 : List Job := [⟨plan2614,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨9,1,(-2)⟩⟩,⟨plan2614,[⟨2,2,0⟩],(some ⟨2,2,0⟩),⟨8,1,0⟩⟩]

def t5_684jobs2 : List Job := [⟨plan2614,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨8,1,(-1)⟩⟩,⟨plan2614,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,1,(-2)⟩⟩]

def t5_684jobs : List Job := t5_684jobs0++t5_684jobs1++t5_684jobs2




def t5_685root : Job := ⟨plan3918,[],none,⟨10,1,0⟩⟩
def t5_685jobs0 : List Job := [⟨plan3918,[],none,⟨10,1,0⟩⟩]

def t5_685jobs : List Job := t5_685jobs0




def t5_686root : Job := ⟨plan3739,[],none,⟨10,0,0⟩⟩
def t5_686jobs0 : List Job := [⟨plan3739,[],none,⟨10,0,0⟩⟩]

def t5_686jobs : List Job := t5_686jobs0




def t5_687root : Job := ⟨plan3919,[],none,⟨10,1,0⟩⟩
def t5_687jobs0 : List Job := [⟨plan3919,[],none,⟨10,1,0⟩⟩]

def t5_687jobs : List Job := t5_687jobs0




def t5_688root : Job := ⟨plan3920,[],none,⟨10,1,0⟩⟩
def t5_688jobs0 : List Job := [⟨plan2618,[⟨2,0,2⟩],(some ⟨2,0,2⟩),⟨10,1,(-2)⟩⟩,⟨plan2618,[⟨2,1,1⟩],(some ⟨2,1,1⟩),⟨9,1,(-1)⟩⟩,⟨plan2618,[⟨2,1,2⟩],(some ⟨2,1,2⟩),⟨9,1,(-2)⟩⟩]

def t5_688jobs1 : List Job := [⟨plan2618,[⟨2,2,0⟩],(some ⟨2,2,0⟩),⟨8,1,0⟩⟩,⟨plan2618,[⟨2,2,1⟩],(some ⟨2,2,1⟩),⟨8,1,(-1)⟩⟩,⟨plan2618,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨8,1,(-2)⟩⟩]

def t5_688jobs : List Job := t5_688jobs0++t5_688jobs1




def t5_689root : Job := ⟨plan3921,[],none,⟨10,1,0⟩⟩
def t5_689jobs0 : List Job := [⟨plan3921,[],none,⟨10,1,0⟩⟩]

def t5_689jobs : List Job := t5_689jobs0




def t5_690root : Job := ⟨plan3922,[],none,⟨10,1,0⟩⟩
def t5_690jobs0 : List Job := [⟨plan3922,[],none,⟨10,1,0⟩⟩]

def t5_690jobs : List Job := t5_690jobs0




def t5_691root : Job := ⟨plan4234,[],none,⟨10,3,0⟩⟩
def t5_691jobs0 : List Job := [⟨plan4234,[],none,⟨10,3,0⟩⟩]

def t5_691jobs : List Job := t5_691jobs0




def t5_692root : Job := ⟨plan4235,[],none,⟨10,3,0⟩⟩
def t5_692jobs0 : List Job := [⟨plan4235,[],none,⟨10,3,0⟩⟩]

def t5_692jobs : List Job := t5_692jobs0




def t5_693root : Job := ⟨plan4236,[],none,⟨10,3,0⟩⟩
def t5_693jobs0 : List Job := [⟨plan4236,[],none,⟨10,3,0⟩⟩]

def t5_693jobs : List Job := t5_693jobs0




def t5_694root : Job := ⟨plan4237,[],none,⟨10,3,0⟩⟩
def t5_694jobs0 : List Job := [⟨plan4237,[],none,⟨10,3,0⟩⟩]

def t5_694jobs : List Job := t5_694jobs0




def t5_695root : Job := ⟨plan4238,[],none,⟨10,3,0⟩⟩
def t5_695jobs0 : List Job := [⟨plan4238,[],none,⟨10,3,0⟩⟩]

def t5_695jobs : List Job := t5_695jobs0




def t5_696root : Job := ⟨plan4239,[],none,⟨10,3,0⟩⟩
def t5_696jobs0 : List Job := [⟨plan4239,[],none,⟨10,3,0⟩⟩]

def t5_696jobs : List Job := t5_696jobs0




def t5_697root : Job := ⟨plan4240,[],none,⟨10,3,0⟩⟩
def t5_697jobs0 : List Job := [⟨plan4240,[],none,⟨10,3,0⟩⟩]

def t5_697jobs : List Job := t5_697jobs0




def t5_698root : Job := ⟨plan4241,[],none,⟨10,3,0⟩⟩
def t5_698jobs0 : List Job := [⟨plan4241,[],none,⟨10,3,0⟩⟩]

def t5_698jobs : List Job := t5_698jobs0




def t5_699root : Job := ⟨plan4242,[],none,⟨10,3,0⟩⟩
def t5_699jobs0 : List Job := [⟨plan4242,[],none,⟨10,3,0⟩⟩]

def t5_699jobs : List Job := t5_699jobs0




def t5_700root : Job := ⟨plan3923,[],none,⟨10,1,0⟩⟩
def t5_700jobs0 : List Job := [⟨plan3923,[],none,⟨10,1,0⟩⟩]

def t5_700jobs : List Job := t5_700jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


