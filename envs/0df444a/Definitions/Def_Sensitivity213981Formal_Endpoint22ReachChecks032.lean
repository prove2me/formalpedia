-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks032
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks032
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:22:51.094532+00:00
-- url     : https://prove2.me/theorems/4bc29362-28d4-4186-85fa-d3e8e93e4c55
-- title:
--   Endpoint22 Reach Checks032 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks032 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t5_983jobs`, `ThreeBoundEndpoint22Reachable.t5_984root`, `ThreeBoundEndpoint22Reachable.t5_984jobs0`, `ThreeBoundEndpoint22Reachable.t5_984jobs1`, `ThreeBoundEndpoint22Reachable.t5_984jobs`, `ThreeBoundEndpoint22Reachable.t5_985root`, `ThreeBoundEndpoint22Reachable.t5_985jobs0`, `ThreeBoundEndpoint22Reachable.t5_985jobs`, `ThreeBoundEndpoint22Reachable.t5_986root`, `ThreeBoundEndpoint22Reachable.t5_986jobs0`, `ThreeBoundEndpoint22Reachable.t5_986jobs`, `ThreeBoundEndpoint22Reachable.t5_987root`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks032.lean, lines 1–421.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans041
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans045
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans049
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

def t5_972root : Job := ⟨plan4342,[],none,⟨10,3,0⟩⟩
def t5_972jobs0 : List Job := [⟨plan2763,[⟨4,0,2⟩],(some ⟨4,0,2⟩),⟨10,1,(-2)⟩⟩,⟨plan2763,[⟨4,1,1⟩],(some ⟨4,1,1⟩),⟨9,2,0⟩⟩]

def t5_972jobs1 : List Job := [⟨plan2763,[⟨4,1,2⟩],(some ⟨4,1,2⟩),⟨9,1,(-1)⟩⟩]

def t5_972jobs : List Job := t5_972jobs0++t5_972jobs1




def t5_973root : Job := ⟨plan4343,[],none,⟨10,3,0⟩⟩
def t5_973jobs0 : List Job := [⟨plan4343,[],none,⟨10,3,0⟩⟩]

def t5_973jobs : List Job := t5_973jobs0




def t5_974root : Job := ⟨plan4344,[],none,⟨10,3,0⟩⟩
def t5_974jobs0 : List Job := [⟨plan4344,[],none,⟨10,3,0⟩⟩]

def t5_974jobs : List Job := t5_974jobs0




def t5_975root : Job := ⟨plan4345,[],none,⟨10,3,0⟩⟩
def t5_975jobs0 : List Job := [⟨plan2766,[⟨4,0,2⟩],(some ⟨4,0,2⟩),⟨10,1,(-2)⟩⟩,⟨plan2766,[⟨4,1,1⟩],(some ⟨4,1,1⟩),⟨9,2,0⟩⟩]

def t5_975jobs1 : List Job := [⟨plan2766,[⟨4,1,2⟩],(some ⟨4,1,2⟩),⟨9,1,(-1)⟩⟩]

def t5_975jobs : List Job := t5_975jobs0++t5_975jobs1




def t5_976root : Job := ⟨plan4346,[],none,⟨10,3,0⟩⟩
def t5_976jobs0 : List Job := [⟨plan4346,[],none,⟨10,3,0⟩⟩]

def t5_976jobs : List Job := t5_976jobs0




def t5_977root : Job := ⟨plan4779,[],none,⟨10,6,0⟩⟩
def t5_977jobs0 : List Job := [⟨plan4779,[],none,⟨10,6,0⟩⟩]

def t5_977jobs : List Job := t5_977jobs0




def t5_978root : Job := ⟨plan4780,[],none,⟨10,6,0⟩⟩
def t5_978jobs0 : List Job := [⟨plan4780,[],none,⟨10,6,0⟩⟩]

def t5_978jobs : List Job := t5_978jobs0




def t5_979root : Job := ⟨plan4781,[],none,⟨10,6,0⟩⟩
def t5_979jobs0 : List Job := [⟨plan4781,[],none,⟨10,6,0⟩⟩]

def t5_979jobs : List Job := t5_979jobs0




def t5_980root : Job := ⟨plan4782,[],none,⟨10,6,0⟩⟩
def t5_980jobs0 : List Job := [⟨plan2907,[⟨4,0,3⟩],(some ⟨4,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2907,[⟨4,1,2⟩],(some ⟨4,1,2⟩),⟨9,4,(-1)⟩⟩]

def t5_980jobs1 : List Job := [⟨plan2907,[⟨4,1,3⟩],(some ⟨4,1,3⟩),⟨9,3,(-2)⟩⟩]

def t5_980jobs : List Job := t5_980jobs0++t5_980jobs1




def t5_981root : Job := ⟨plan4783,[],none,⟨10,6,0⟩⟩
def t5_981jobs0 : List Job := [⟨plan2908,[⟨4,0,3⟩],(some ⟨4,0,3⟩),⟨10,3,(-3)⟩⟩]

def t5_981jobs1 : List Job := [⟨plan2908,[⟨4,1,2⟩],(some ⟨4,1,2⟩),⟨9,4,(-1)⟩⟩]

def t5_981jobs2 : List Job := [⟨plan2908,[⟨4,1,3⟩],(some ⟨4,1,3⟩),⟨9,3,(-2)⟩⟩]

def t5_981jobs : List Job := t5_981jobs0++t5_981jobs1++t5_981jobs2




def t5_982root : Job := ⟨plan4784,[],none,⟨10,6,0⟩⟩
def t5_982jobs0 : List Job := [⟨plan4784,[],none,⟨10,6,0⟩⟩]

def t5_982jobs : List Job := t5_982jobs0




def t5_983root : Job := ⟨plan4785,[],none,⟨10,6,0⟩⟩
def t5_983jobs0 : List Job := [⟨plan4785,[],none,⟨10,6,0⟩⟩]

def t5_983jobs : List Job := t5_983jobs0




def t5_984root : Job := ⟨plan4786,[],none,⟨10,6,0⟩⟩
def t5_984jobs0 : List Job := [⟨plan2911,[⟨4,0,3⟩],(some ⟨4,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2911,[⟨4,1,2⟩],(some ⟨4,1,2⟩),⟨9,4,(-1)⟩⟩]

def t5_984jobs1 : List Job := [⟨plan2911,[⟨4,1,3⟩],(some ⟨4,1,3⟩),⟨9,3,(-2)⟩⟩]

def t5_984jobs : List Job := t5_984jobs0++t5_984jobs1




def t5_985root : Job := ⟨plan4787,[],none,⟨10,6,0⟩⟩
def t5_985jobs0 : List Job := [⟨plan4787,[],none,⟨10,6,0⟩⟩]

def t5_985jobs : List Job := t5_985jobs0




def t5_986root : Job := ⟨plan4788,[],none,⟨10,6,0⟩⟩
def t5_986jobs0 : List Job := [⟨plan4788,[],none,⟨10,6,0⟩⟩]

def t5_986jobs : List Job := t5_986jobs0




def t5_987root : Job := ⟨plan4347,[],none,⟨10,3,0⟩⟩
def t5_987jobs0 : List Job := [⟨plan4347,[],none,⟨10,3,0⟩⟩]

def t5_987jobs : List Job := t5_987jobs0




def t5_988root : Job := ⟨plan3965,[],none,⟨10,1,0⟩⟩
def t5_988jobs0 : List Job := [⟨plan3965,[],none,⟨10,1,0⟩⟩]

def t5_988jobs : List Job := t5_988jobs0




def t5_989root : Job := ⟨plan4348,[],none,⟨10,3,0⟩⟩
def t5_989jobs0 : List Job := [⟨plan4348,[],none,⟨10,3,0⟩⟩]

def t5_989jobs : List Job := t5_989jobs0




def t5_990root : Job := ⟨plan4349,[],none,⟨10,3,0⟩⟩
def t5_990jobs0 : List Job := [⟨plan4349,[],none,⟨10,3,0⟩⟩]

def t5_990jobs : List Job := t5_990jobs0




def t5_991root : Job := ⟨plan4350,[],none,⟨10,3,0⟩⟩
def t5_991jobs0 : List Job := [⟨plan4350,[],none,⟨10,3,0⟩⟩]

def t5_991jobs : List Job := t5_991jobs0




def t5_992root : Job := ⟨plan4789,[],none,⟨10,6,0⟩⟩
def t5_992jobs0 : List Job := [⟨plan4789,[],none,⟨10,6,0⟩⟩]

def t5_992jobs : List Job := t5_992jobs0




def t5_993root : Job := ⟨plan4790,[],none,⟨10,6,0⟩⟩
def t5_993jobs0 : List Job := [⟨plan4790,[],none,⟨10,6,0⟩⟩]

def t5_993jobs : List Job := t5_993jobs0




def t5_994root : Job := ⟨plan4791,[],none,⟨10,6,0⟩⟩
def t5_994jobs0 : List Job := [⟨plan4791,[],none,⟨10,6,0⟩⟩]

def t5_994jobs : List Job := t5_994jobs0




def t5_995root : Job := ⟨plan4792,[],none,⟨10,6,0⟩⟩
def t5_995jobs0 : List Job := [⟨plan4792,[],none,⟨10,6,0⟩⟩]

def t5_995jobs : List Job := t5_995jobs0




def t5_996root : Job := ⟨plan4793,[],none,⟨10,6,0⟩⟩
def t5_996jobs0 : List Job := [⟨plan4793,[],none,⟨10,6,0⟩⟩]

def t5_996jobs : List Job := t5_996jobs0




def t5_997root : Job := ⟨plan4794,[],none,⟨10,6,0⟩⟩
def t5_997jobs0 : List Job := [⟨plan4794,[],none,⟨10,6,0⟩⟩]

def t5_997jobs : List Job := t5_997jobs0




def t5_998root : Job := ⟨plan4795,[],none,⟨10,6,0⟩⟩
def t5_998jobs0 : List Job := [⟨plan4795,[],none,⟨10,6,0⟩⟩]

def t5_998jobs : List Job := t5_998jobs0




def t5_999root : Job := ⟨plan4796,[],none,⟨10,6,0⟩⟩
def t5_999jobs0 : List Job := [⟨plan4796,[],none,⟨10,6,0⟩⟩]

def t5_999jobs : List Job := t5_999jobs0




def t5_1000root : Job := ⟨plan3966,[],none,⟨10,1,0⟩⟩
def t5_1000jobs0 : List Job := [⟨plan3966,[],none,⟨10,1,0⟩⟩]

def t5_1000jobs : List Job := t5_1000jobs0




def t5_1001root : Job := ⟨plan4351,[],none,⟨10,3,0⟩⟩
def t5_1001jobs0 : List Job := [⟨plan4351,[],none,⟨10,3,0⟩⟩]

def t5_1001jobs : List Job := t5_1001jobs0




def t5_1002root : Job := ⟨plan4352,[],none,⟨10,3,0⟩⟩
def t5_1002jobs0 : List Job := [⟨plan4352,[],none,⟨10,3,0⟩⟩]

def t5_1002jobs : List Job := t5_1002jobs0




def t5_1003root : Job := ⟨plan4353,[],none,⟨10,3,0⟩⟩
def t5_1003jobs0 : List Job := [⟨plan4353,[],none,⟨10,3,0⟩⟩]

def t5_1003jobs : List Job := t5_1003jobs0




def t5_1004root : Job := ⟨plan4797,[],none,⟨10,6,0⟩⟩
def t5_1004jobs0 : List Job := [⟨plan4797,[],none,⟨10,6,0⟩⟩]

def t5_1004jobs : List Job := t5_1004jobs0




def t5_1005root : Job := ⟨plan4798,[],none,⟨10,6,0⟩⟩
def t5_1005jobs0 : List Job := [⟨plan4798,[],none,⟨10,6,0⟩⟩]

def t5_1005jobs : List Job := t5_1005jobs0




def t5_1006root : Job := ⟨plan4799,[],none,⟨10,6,0⟩⟩
def t5_1006jobs0 : List Job := [⟨plan4799,[],none,⟨10,6,0⟩⟩]

def t5_1006jobs : List Job := t5_1006jobs0




def t5_1007root : Job := ⟨plan4800,[],none,⟨10,6,0⟩⟩
def t5_1007jobs0 : List Job := [⟨plan4800,[],none,⟨10,6,0⟩⟩]

def t5_1007jobs : List Job := t5_1007jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


