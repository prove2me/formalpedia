-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks086
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks086
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:28:30.498061+00:00
-- url     : https://prove2.me/theorems/abe0f4c1-ea0c-47a0-b116-f9117c7d3ce6
-- title:
--   Endpoint22 Reach Checks086 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks086 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_691jobs2`, `ThreeBoundEndpoint22Reachable.t6_702root`, `ThreeBoundEndpoint22Reachable.t6_702jobs0`, `ThreeBoundEndpoint22Reachable.t6_702jobs`, `ThreeBoundEndpoint22Reachable.t6_703root`, `ThreeBoundEndpoint22Reachable.t6_703jobs0`, `ThreeBoundEndpoint22Reachable.t6_703jobs`, `ThreeBoundEndpoint22Reachable.t6_704root`, `ThreeBoundEndpoint22Reachable.t6_704jobs0`, `ThreeBoundEndpoint22Reachable.t6_691jobs`, `ThreeBoundEndpoint22Reachable.t6_704jobs`, `ThreeBoundEndpoint22Reachable.t6_705root`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks086.lean, lines 1–336.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans072
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans076
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

def t6_691root : Job := ⟨plan6940,[],none,⟨15,6,0⟩⟩
def t6_691jobs0 : List Job := [⟨plan5682,[⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5682,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨14,6,(-3)⟩⟩,⟨plan5682,[⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨14,6,(-4)⟩⟩]

def t6_691jobs1 : List Job := [⟨plan5682,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨13,6,(-2)⟩⟩]

def t6_691jobs2 : List Job := [⟨plan5682,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨13,6,(-3)⟩⟩]

def t6_691jobs : List Job := t6_691jobs0++t6_691jobs1++t6_691jobs2




def t6_692root : Job := ⟨plan6941,[],none,⟨15,6,0⟩⟩
def t6_692jobs0 : List Job := [⟨plan6941,[],none,⟨15,6,0⟩⟩]

def t6_692jobs : List Job := t6_692jobs0




def t6_693root : Job := ⟨plan6942,[],none,⟨15,6,0⟩⟩
def t6_693jobs0 : List Job := [⟨plan5684,[⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5684,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨14,6,(-3)⟩⟩,⟨plan5684,[⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨14,6,(-4)⟩⟩]

def t6_693jobs1 : List Job := [⟨plan5684,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨13,6,(-2)⟩⟩]

def t6_693jobs2 : List Job := [⟨plan5684,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨13,6,(-3)⟩⟩]

def t6_693jobs : List Job := t6_693jobs0++t6_693jobs1++t6_693jobs2




def t6_694root : Job := ⟨plan6943,[],none,⟨15,6,0⟩⟩
def t6_694jobs0 : List Job := [⟨plan5685,[⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5685,[⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨14,6,(-3)⟩⟩,⟨plan5685,[⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨14,6,(-4)⟩⟩]

def t6_694jobs1 : List Job := [⟨plan5685,[⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨13,6,(-2)⟩⟩]

def t6_694jobs2 : List Job := [⟨plan5685,[⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨13,6,(-3)⟩⟩]

def t6_694jobs : List Job := t6_694jobs0++t6_694jobs1++t6_694jobs2




def t6_695root : Job := ⟨plan6944,[],none,⟨15,6,0⟩⟩
def t6_695jobs0 : List Job := [⟨plan6944,[],none,⟨15,6,0⟩⟩]

def t6_695jobs : List Job := t6_695jobs0




def t6_696root : Job := ⟨plan6945,[],none,⟨15,6,0⟩⟩
def t6_696jobs0 : List Job := [⟨plan6945,[],none,⟨15,6,0⟩⟩]

def t6_696jobs : List Job := t6_696jobs0




def t6_697root : Job := ⟨plan7320,[],none,⟨15,10,0⟩⟩
def t6_697jobs0 : List Job := [⟨plan7320,[],none,⟨15,10,0⟩⟩]

def t6_697jobs : List Job := t6_697jobs0




def t6_698root : Job := ⟨plan7321,[],none,⟨15,10,0⟩⟩
def t6_698jobs0 : List Job := [⟨plan7321,[],none,⟨15,10,0⟩⟩]

def t6_698jobs : List Job := t6_698jobs0




def t6_699root : Job := ⟨plan7322,[],none,⟨15,10,0⟩⟩
def t6_699jobs0 : List Job := [⟨plan7322,[],none,⟨15,10,0⟩⟩]

def t6_699jobs : List Job := t6_699jobs0




def t6_700root : Job := ⟨plan7323,[],none,⟨15,10,0⟩⟩
def t6_700jobs0 : List Job := [⟨plan7323,[],none,⟨15,10,0⟩⟩]

def t6_700jobs : List Job := t6_700jobs0




def t6_701root : Job := ⟨plan7324,[],none,⟨15,10,0⟩⟩
def t6_701jobs0 : List Job := [⟨plan7324,[],none,⟨15,10,0⟩⟩]

def t6_701jobs : List Job := t6_701jobs0




def t6_702root : Job := ⟨plan7325,[],none,⟨15,10,0⟩⟩
def t6_702jobs0 : List Job := [⟨plan7325,[],none,⟨15,10,0⟩⟩]

def t6_702jobs : List Job := t6_702jobs0




def t6_703root : Job := ⟨plan7326,[],none,⟨15,10,0⟩⟩
def t6_703jobs0 : List Job := [⟨plan7326,[],none,⟨15,10,0⟩⟩]

def t6_703jobs : List Job := t6_703jobs0




def t6_704root : Job := ⟨plan7327,[],none,⟨15,10,0⟩⟩
def t6_704jobs0 : List Job := [⟨plan7327,[],none,⟨15,10,0⟩⟩]

def t6_704jobs : List Job := t6_704jobs0




def t6_705root : Job := ⟨plan7328,[],none,⟨15,10,0⟩⟩
def t6_705jobs0 : List Job := [⟨plan7328,[],none,⟨15,10,0⟩⟩]

def t6_705jobs : List Job := t6_705jobs0




def t6_706root : Job := ⟨plan7329,[],none,⟨15,10,0⟩⟩
def t6_706jobs0 : List Job := [⟨plan7329,[],none,⟨15,10,0⟩⟩]

def t6_706jobs : List Job := t6_706jobs0




def t6_707root : Job := ⟨plan6946,[],none,⟨15,6,0⟩⟩
def t6_707jobs0 : List Job := [⟨plan6946,[],none,⟨15,6,0⟩⟩]

def t6_707jobs : List Job := t6_707jobs0




def t6_708root : Job := ⟨plan7330,[],none,⟨15,10,0⟩⟩
def t6_708jobs0 : List Job := [⟨plan7330,[],none,⟨15,10,0⟩⟩]

def t6_708jobs : List Job := t6_708jobs0




def t6_709root : Job := ⟨plan7331,[],none,⟨15,10,0⟩⟩
def t6_709jobs0 : List Job := [⟨plan7331,[],none,⟨15,10,0⟩⟩]

def t6_709jobs : List Job := t6_709jobs0




def t6_710root : Job := ⟨plan7332,[],none,⟨15,10,0⟩⟩
def t6_710jobs0 : List Job := [⟨plan7332,[],none,⟨15,10,0⟩⟩]

def t6_710jobs : List Job := t6_710jobs0




def t6_711root : Job := ⟨plan7333,[],none,⟨15,10,0⟩⟩
def t6_711jobs0 : List Job := [⟨plan7333,[],none,⟨15,10,0⟩⟩]

def t6_711jobs : List Job := t6_711jobs0




def t6_712root : Job := ⟨plan7334,[],none,⟨15,10,0⟩⟩
def t6_712jobs0 : List Job := [⟨plan7334,[],none,⟨15,10,0⟩⟩]

def t6_712jobs : List Job := t6_712jobs0




def t6_713root : Job := ⟨plan7335,[],none,⟨15,10,0⟩⟩
def t6_713jobs0 : List Job := [⟨plan7335,[],none,⟨15,10,0⟩⟩]

def t6_713jobs : List Job := t6_713jobs0




def t6_714root : Job := ⟨plan7336,[],none,⟨15,10,0⟩⟩
def t6_714jobs0 : List Job := [⟨plan7336,[],none,⟨15,10,0⟩⟩]

def t6_714jobs : List Job := t6_714jobs0




def t6_715root : Job := ⟨plan7337,[],none,⟨15,10,0⟩⟩
def t6_715jobs0 : List Job := [⟨plan7337,[],none,⟨15,10,0⟩⟩]

def t6_715jobs : List Job := t6_715jobs0




def t6_716root : Job := ⟨plan7338,[],none,⟨15,10,0⟩⟩
def t6_716jobs0 : List Job := [⟨plan7338,[],none,⟨15,10,0⟩⟩]

def t6_716jobs : List Job := t6_716jobs0




def t6_717root : Job := ⟨plan7339,[],none,⟨15,10,0⟩⟩
def t6_717jobs0 : List Job := [⟨plan3478,[⟨2,0,5⟩,⟨5,0,4⟩],(some ⟨5,0,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3478,[⟨2,0,5⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3478,[⟨2,0,5⟩,⟨5,1,4⟩],(some ⟨5,1,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3478,[⟨2,0,5⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨13,8,(-5)⟩⟩,⟨plan3478,[⟨2,0,5⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3478,[⟨2,1,4⟩,⟨5,0,4⟩],(some ⟨5,0,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3478,[⟨2,1,4⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3478,[⟨2,1,4⟩,⟨5,1,4⟩],(some ⟨5,1,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3478,[⟨2,1,4⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨12,8,(-4)⟩⟩,⟨plan3478,[⟨2,1,4⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3478,[⟨2,2,3⟩,⟨5,0,4⟩],(some ⟨5,0,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3478,[⟨2,2,3⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3478,[⟨2,2,3⟩,⟨5,1,4⟩],(some ⟨5,1,4⟩),⟨12,6,(-6)⟩⟩]

def t6_717jobs1 : List Job := [⟨plan3478,[⟨2,2,3⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨11,8,(-3)⟩⟩,⟨plan3478,[⟨2,2,3⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨11,7,(-4)⟩⟩]

def t6_717jobs : List Job := t6_717jobs0++t6_717jobs1




def t6_718root : Job := ⟨plan7340,[],none,⟨15,10,0⟩⟩
def t6_718jobs0 : List Job := [⟨plan3479,[⟨2,0,5⟩,⟨5,0,4⟩],(some ⟨5,0,4⟩),⟨15,6,(-9)⟩⟩,⟨plan3479,[⟨2,0,5⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨14,7,(-7)⟩⟩,⟨plan3479,[⟨2,0,5⟩,⟨5,1,4⟩],(some ⟨5,1,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3479,[⟨2,0,5⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨13,8,(-5)⟩⟩,⟨plan3479,[⟨2,0,5⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3479,[⟨2,1,4⟩,⟨5,0,4⟩],(some ⟨5,0,4⟩),⟨14,6,(-8)⟩⟩,⟨plan3479,[⟨2,1,4⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨13,7,(-6)⟩⟩,⟨plan3479,[⟨2,1,4⟩,⟨5,1,4⟩],(some ⟨5,1,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3479,[⟨2,1,4⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨12,8,(-4)⟩⟩,⟨plan3479,[⟨2,1,4⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3479,[⟨2,2,3⟩,⟨5,0,4⟩],(some ⟨5,0,4⟩),⟨13,6,(-7)⟩⟩,⟨plan3479,[⟨2,2,3⟩,⟨5,1,3⟩],(some ⟨5,1,3⟩),⟨12,7,(-5)⟩⟩,⟨plan3479,[⟨2,2,3⟩,⟨5,1,4⟩],(some ⟨5,1,4⟩),⟨12,6,(-6)⟩⟩]

def t6_718jobs1 : List Job := [⟨plan3479,[⟨2,2,3⟩,⟨5,2,2⟩],(some ⟨5,2,2⟩),⟨11,8,(-3)⟩⟩,⟨plan3479,[⟨2,2,3⟩,⟨5,2,3⟩],(some ⟨5,2,3⟩),⟨11,7,(-4)⟩⟩]

def t6_718jobs : List Job := t6_718jobs0++t6_718jobs1



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


