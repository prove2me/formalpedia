-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks120
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks120
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:29:43.718523+00:00
-- url     : https://prove2.me/theorems/f3d506c4-3fee-40a0-b89e-a01cd0d6c881
-- title:
--   Endpoint22 Reach Checks120 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks120 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_993root`, `ThreeBoundEndpoint22Reachable.t6_993jobs0`, `ThreeBoundEndpoint22Reachable.t6_993jobs`, `ThreeBoundEndpoint22Reachable.t6_994root`, `ThreeBoundEndpoint22Reachable.t6_994jobs0`, `ThreeBoundEndpoint22Reachable.t6_994jobs`, `ThreeBoundEndpoint22Reachable.t6_995root`, `ThreeBoundEndpoint22Reachable.t6_995jobs0`, `ThreeBoundEndpoint22Reachable.t6_995jobs`, `ThreeBoundEndpoint22Reachable.t6_996root`, `ThreeBoundEndpoint22Reachable.t6_996jobs0`, `ThreeBoundEndpoint22Reachable.t6_996jobs`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks120.lean, lines 1–264.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
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

def t6_984root : Job := ⟨plan7468,[],none,⟨15,10,0⟩⟩
def t6_984jobs0 : List Job := [⟨plan5774,[⟨4,0,4⟩],(some ⟨4,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5774,[⟨4,1,3⟩],(some ⟨4,1,3⟩),⟨14,7,(-2)⟩⟩]

def t6_984jobs1 : List Job := [⟨plan5774,[⟨4,1,4⟩],(some ⟨4,1,4⟩),⟨14,6,(-3)⟩⟩]

def t6_984jobs : List Job := t6_984jobs0++t6_984jobs1




def t6_985root : Job := ⟨plan7469,[],none,⟨15,10,0⟩⟩
def t6_985jobs0 : List Job := [⟨plan7469,[],none,⟨15,10,0⟩⟩]

def t6_985jobs : List Job := t6_985jobs0




def t6_986root : Job := ⟨plan7470,[],none,⟨15,10,0⟩⟩
def t6_986jobs0 : List Job := [⟨plan5776,[⟨4,0,4⟩],(some ⟨4,0,4⟩),⟨15,6,(-4)⟩⟩]

def t6_986jobs1 : List Job := [⟨plan5776,[⟨4,1,3⟩],(some ⟨4,1,3⟩),⟨14,7,(-2)⟩⟩]

def t6_986jobs2 : List Job := [⟨plan5776,[⟨4,1,4⟩],(some ⟨4,1,4⟩),⟨14,6,(-3)⟩⟩]

def t6_986jobs : List Job := t6_986jobs0++t6_986jobs1++t6_986jobs2




def t6_987root : Job := ⟨plan7471,[],none,⟨15,10,0⟩⟩
def t6_987jobs0 : List Job := [⟨plan3482,[⟨4,0,4⟩,⟨3,0,5⟩],(some ⟨3,0,5⟩),⟨15,6,(-9)⟩⟩,⟨plan3482,[⟨4,0,4⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3482,[⟨4,0,4⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨13,6,(-7)⟩⟩,⟨plan3482,[⟨4,0,4⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨12,6,(-6)⟩⟩,⟨plan3482,[⟨4,1,3⟩,⟨3,0,5⟩],(some ⟨3,0,5⟩),⟨14,7,(-7)⟩⟩,⟨plan3482,[⟨4,1,3⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨13,7,(-6)⟩⟩,⟨plan3482,[⟨4,1,3⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,7,(-5)⟩⟩]

def t6_987jobs1 : List Job := [⟨plan3482,[⟨4,1,3⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,7,(-4)⟩⟩,⟨plan3482,[⟨4,1,4⟩,⟨3,0,5⟩],(some ⟨3,0,5⟩),⟨14,6,(-8)⟩⟩,⟨plan3482,[⟨4,1,4⟩,⟨3,1,4⟩],(some ⟨3,1,4⟩),⟨13,6,(-7)⟩⟩]

def t6_987jobs2 : List Job := [⟨plan3482,[⟨4,1,4⟩,⟨3,2,3⟩],(some ⟨3,2,3⟩),⟨12,6,(-6)⟩⟩,⟨plan3482,[⟨4,1,4⟩,⟨3,3,2⟩],(some ⟨3,3,2⟩),⟨11,6,(-5)⟩⟩]

def t6_987jobs : List Job := t6_987jobs0++t6_987jobs1++t6_987jobs2




def t6_988root : Job := ⟨plan7472,[],none,⟨15,10,0⟩⟩
def t6_988jobs0 : List Job := [⟨plan5778,[⟨4,0,4⟩],(some ⟨4,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5778,[⟨4,1,3⟩],(some ⟨4,1,3⟩),⟨14,7,(-2)⟩⟩]

def t6_988jobs1 : List Job := [⟨plan5778,[⟨4,1,4⟩],(some ⟨4,1,4⟩),⟨14,6,(-3)⟩⟩]

def t6_988jobs : List Job := t6_988jobs0++t6_988jobs1




def t6_989root : Job := ⟨plan7473,[],none,⟨15,10,0⟩⟩
def t6_989jobs0 : List Job := [⟨plan7473,[],none,⟨15,10,0⟩⟩]

def t6_989jobs : List Job := t6_989jobs0




def t6_990root : Job := ⟨plan7474,[],none,⟨15,10,0⟩⟩
def t6_990jobs0 : List Job := [⟨plan5780,[⟨4,0,4⟩],(some ⟨4,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5780,[⟨4,1,3⟩],(some ⟨4,1,3⟩),⟨14,7,(-2)⟩⟩]

def t6_990jobs1 : List Job := [⟨plan5780,[⟨4,1,4⟩],(some ⟨4,1,4⟩),⟨14,6,(-3)⟩⟩]

def t6_990jobs : List Job := t6_990jobs0++t6_990jobs1




def t6_991root : Job := ⟨plan7475,[],none,⟨15,10,0⟩⟩
def t6_991jobs0 : List Job := [⟨plan5781,[⟨4,0,4⟩],(some ⟨4,0,4⟩),⟨15,6,(-4)⟩⟩]

def t6_991jobs1 : List Job := [⟨plan5781,[⟨4,1,3⟩],(some ⟨4,1,3⟩),⟨14,7,(-2)⟩⟩]

def t6_991jobs2 : List Job := [⟨plan5781,[⟨4,1,4⟩],(some ⟨4,1,4⟩),⟨14,6,(-3)⟩⟩]

def t6_991jobs : List Job := t6_991jobs0++t6_991jobs1++t6_991jobs2




def t6_992root : Job := ⟨plan7476,[],none,⟨15,10,0⟩⟩
def t6_992jobs0 : List Job := [⟨plan5782,[⟨4,0,4⟩],(some ⟨4,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5782,[⟨4,1,3⟩],(some ⟨4,1,3⟩),⟨14,7,(-2)⟩⟩]

def t6_992jobs1 : List Job := [⟨plan5782,[⟨4,1,4⟩],(some ⟨4,1,4⟩),⟨14,6,(-3)⟩⟩]

def t6_992jobs : List Job := t6_992jobs0++t6_992jobs1




def t6_993root : Job := ⟨plan7477,[],none,⟨15,10,0⟩⟩
def t6_993jobs0 : List Job := [⟨plan7477,[],none,⟨15,10,0⟩⟩]

def t6_993jobs : List Job := t6_993jobs0




def t6_994root : Job := ⟨plan7478,[],none,⟨15,10,0⟩⟩
def t6_994jobs0 : List Job := [⟨plan7478,[],none,⟨15,10,0⟩⟩]

def t6_994jobs : List Job := t6_994jobs0




def t6_995root : Job := ⟨plan7020,[],none,⟨15,6,0⟩⟩
def t6_995jobs0 : List Job := [⟨plan7020,[],none,⟨15,6,0⟩⟩]

def t6_995jobs : List Job := t6_995jobs0




def t6_996root : Job := ⟨plan7479,[],none,⟨15,10,0⟩⟩
def t6_996jobs0 : List Job := [⟨plan7479,[],none,⟨15,10,0⟩⟩]

def t6_996jobs : List Job := t6_996jobs0




def t6_997root : Job := ⟨plan7480,[],none,⟨15,10,0⟩⟩
def t6_997jobs0 : List Job := [⟨plan7480,[],none,⟨15,10,0⟩⟩]

def t6_997jobs : List Job := t6_997jobs0




def t6_998root : Job := ⟨plan7481,[],none,⟨15,10,0⟩⟩
def t6_998jobs0 : List Job := [⟨plan7481,[],none,⟨15,10,0⟩⟩]

def t6_998jobs : List Job := t6_998jobs0




def t6_999root : Job := ⟨plan6636,[],none,⟨15,3,0⟩⟩
def t6_999jobs0 : List Job := [⟨plan6636,[],none,⟨15,3,0⟩⟩]

def t6_999jobs : List Job := t6_999jobs0




def t6_1000root : Job := ⟨plan7021,[],none,⟨15,6,0⟩⟩
def t6_1000jobs0 : List Job := [⟨plan7021,[],none,⟨15,6,0⟩⟩]

def t6_1000jobs : List Job := t6_1000jobs0




def t6_1001root : Job := ⟨plan7022,[],none,⟨15,6,0⟩⟩
def t6_1001jobs0 : List Job := [⟨plan7022,[],none,⟨15,6,0⟩⟩]

def t6_1001jobs : List Job := t6_1001jobs0




def t6_1002root : Job := ⟨plan7023,[],none,⟨15,6,0⟩⟩
def t6_1002jobs0 : List Job := [⟨plan7023,[],none,⟨15,6,0⟩⟩]

def t6_1002jobs : List Job := t6_1002jobs0




def t6_1003root : Job := ⟨plan7482,[],none,⟨15,10,0⟩⟩
def t6_1003jobs0 : List Job := [⟨plan7482,[],none,⟨15,10,0⟩⟩]

def t6_1003jobs : List Job := t6_1003jobs0




def t6_1004root : Job := ⟨plan7483,[],none,⟨15,10,0⟩⟩
def t6_1004jobs0 : List Job := [⟨plan7483,[],none,⟨15,10,0⟩⟩]

def t6_1004jobs : List Job := t6_1004jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


