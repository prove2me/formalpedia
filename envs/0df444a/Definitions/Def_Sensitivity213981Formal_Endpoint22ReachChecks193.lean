-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks193
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks193
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:34:32.242934+00:00
-- url     : https://prove2.me/theorems/0bac5774-a1bf-4777-9f9f-2a8256dde121
-- title:
--   Endpoint22 Reach Checks193 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks193 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t7_674root`, `ThreeBoundEndpoint22Reachable.t7_674jobs0`, `ThreeBoundEndpoint22Reachable.t7_674jobs`, `ThreeBoundEndpoint22Reachable.t7_675root`, `ThreeBoundEndpoint22Reachable.t7_663jobs2`, `ThreeBoundEndpoint22Reachable.t7_675jobs0`, `ThreeBoundEndpoint22Reachable.t7_675jobs`, `ThreeBoundEndpoint22Reachable.t7_676root`, `ThreeBoundEndpoint22Reachable.t7_676jobs0`, `ThreeBoundEndpoint22Reachable.t7_676jobs`, `ThreeBoundEndpoint22Reachable.t7_677root`, `ThreeBoundEndpoint22Reachable.t7_677jobs0`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks193.lean, lines 1–762.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans089
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans090
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans093
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans094
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans095
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

def t7_663root : Job := ⟨plan8931,[],none,⟨21,15,0⟩⟩
def t7_663jobs0 : List Job := [⟨plan8240,[⟨9,0,5⟩],(some ⟨9,0,5⟩),⟨21,10,(-5)⟩⟩,⟨plan8240,[⟨9,1,4⟩],(some ⟨9,1,4⟩),⟨20,11,(-3)⟩⟩,⟨plan8240,[⟨9,1,5⟩],(some ⟨9,1,5⟩),⟨20,10,(-4)⟩⟩]

def t7_663jobs1 : List Job := [⟨plan8240,[⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨19,12,(-1)⟩⟩]

def t7_663jobs2 : List Job := [⟨plan8240,[⟨9,2,4⟩],(some ⟨9,2,4⟩),⟨19,11,(-2)⟩⟩]

def t7_663jobs : List Job := t7_663jobs0++t7_663jobs1++t7_663jobs2




def t7_664root : Job := ⟨plan8932,[],none,⟨21,15,0⟩⟩
def t7_664jobs0 : List Job := [⟨plan8241,[⟨9,0,5⟩],(some ⟨9,0,5⟩),⟨21,10,(-5)⟩⟩,⟨plan8241,[⟨9,1,4⟩],(some ⟨9,1,4⟩),⟨20,11,(-3)⟩⟩,⟨plan8241,[⟨9,1,5⟩],(some ⟨9,1,5⟩),⟨20,10,(-4)⟩⟩]

def t7_664jobs1 : List Job := [⟨plan8241,[⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨19,12,(-1)⟩⟩]

def t7_664jobs2 : List Job := [⟨plan8241,[⟨9,2,4⟩],(some ⟨9,2,4⟩),⟨19,11,(-2)⟩⟩]

def t7_664jobs : List Job := t7_664jobs0++t7_664jobs1++t7_664jobs2




def t7_665root : Job := ⟨plan8933,[],none,⟨21,15,0⟩⟩
def t7_665jobs0 : List Job := [⟨plan8242,[⟨9,0,5⟩],(some ⟨9,0,5⟩),⟨21,10,(-5)⟩⟩,⟨plan8242,[⟨9,1,4⟩],(some ⟨9,1,4⟩),⟨20,11,(-3)⟩⟩,⟨plan8242,[⟨9,1,5⟩],(some ⟨9,1,5⟩),⟨20,10,(-4)⟩⟩,⟨plan8242,[⟨9,2,3⟩],(some ⟨9,2,3⟩),⟨19,12,(-1)⟩⟩]

def t7_665jobs1 : List Job := [⟨plan8242,[⟨9,2,4⟩],(some ⟨9,2,4⟩),⟨19,11,(-2)⟩⟩]

def t7_665jobs : List Job := t7_665jobs0++t7_665jobs1




def t7_666root : Job := ⟨plan8934,[],none,⟨21,15,0⟩⟩
def t7_666jobs0 : List Job := [⟨plan8934,[],none,⟨21,15,0⟩⟩]

def t7_666jobs : List Job := t7_666jobs0




def t7_667root : Job := ⟨plan8935,[],none,⟨21,15,0⟩⟩
def t7_667jobs0 : List Job := [⟨plan8935,[],none,⟨21,15,0⟩⟩]

def t7_667jobs : List Job := t7_667jobs0




def t7_668root : Job := ⟨plan9091,[],none,⟨21,21,0⟩⟩
def t7_668jobs0 : List Job := [⟨plan9091,[],none,⟨21,21,0⟩⟩]

def t7_668jobs : List Job := t7_668jobs0




def t7_669root : Job := ⟨plan9092,[],none,⟨21,21,0⟩⟩
def t7_669jobs0 : List Job := [⟨plan9092,[],none,⟨21,21,0⟩⟩]

def t7_669jobs : List Job := t7_669jobs0




def t7_670root : Job := ⟨plan9093,[],none,⟨21,21,0⟩⟩
def t7_670jobs0 : List Job := [⟨plan9093,[],none,⟨21,21,0⟩⟩]

def t7_670jobs : List Job := t7_670jobs0




def t7_671root : Job := ⟨plan9094,[],none,⟨21,21,0⟩⟩
def t7_671jobs0 : List Job := [⟨plan9094,[],none,⟨21,21,0⟩⟩]

def t7_671jobs : List Job := t7_671jobs0




def t7_672root : Job := ⟨plan9095,[],none,⟨21,21,0⟩⟩
def t7_672jobs0 : List Job := [⟨plan9095,[],none,⟨21,21,0⟩⟩]

def t7_672jobs : List Job := t7_672jobs0




def t7_673root : Job := ⟨plan9096,[],none,⟨21,21,0⟩⟩
def t7_673jobs0 : List Job := [⟨plan9096,[],none,⟨21,21,0⟩⟩]

def t7_673jobs : List Job := t7_673jobs0




def t7_674root : Job := ⟨plan9097,[],none,⟨21,21,0⟩⟩
def t7_674jobs0 : List Job := [⟨plan9097,[],none,⟨21,21,0⟩⟩]

def t7_674jobs : List Job := t7_674jobs0




def t7_675root : Job := ⟨plan9098,[],none,⟨21,21,0⟩⟩
def t7_675jobs0 : List Job := [⟨plan9098,[],none,⟨21,21,0⟩⟩]

def t7_675jobs : List Job := t7_675jobs0




def t7_676root : Job := ⟨plan9099,[],none,⟨21,21,0⟩⟩
def t7_676jobs0 : List Job := [⟨plan9099,[],none,⟨21,21,0⟩⟩]

def t7_676jobs : List Job := t7_676jobs0




def t7_677root : Job := ⟨plan9100,[],none,⟨21,21,0⟩⟩
def t7_677jobs0 : List Job := [⟨plan9100,[],none,⟨21,21,0⟩⟩]

def t7_677jobs : List Job := t7_677jobs0




def t7_678root : Job := ⟨plan9101,[],none,⟨21,21,0⟩⟩
def t7_678jobs0 : List Job := [⟨plan9101,[],none,⟨21,21,0⟩⟩]

def t7_678jobs : List Job := t7_678jobs0




def t7_679root : Job := ⟨plan9102,[],none,⟨21,21,0⟩⟩
def t7_679jobs0 : List Job := [⟨plan9102,[],none,⟨21,21,0⟩⟩]

def t7_679jobs : List Job := t7_679jobs0




def t7_680root : Job := ⟨plan9103,[],none,⟨21,21,0⟩⟩
def t7_680jobs0 : List Job := [⟨plan9103,[],none,⟨21,21,0⟩⟩]

def t7_680jobs : List Job := t7_680jobs0




def t7_681root : Job := ⟨plan9104,[],none,⟨21,21,0⟩⟩
def t7_681jobs0 : List Job := [⟨plan9104,[],none,⟨21,21,0⟩⟩]

def t7_681jobs : List Job := t7_681jobs0




def t7_682root : Job := ⟨plan9105,[],none,⟨21,21,0⟩⟩
def t7_682jobs0 : List Job := [⟨plan9105,[],none,⟨21,21,0⟩⟩]

def t7_682jobs : List Job := t7_682jobs0




def t7_683root : Job := ⟨plan9106,[],none,⟨21,21,0⟩⟩
def t7_683jobs0 : List Job := [⟨plan9106,[],none,⟨21,21,0⟩⟩]

def t7_683jobs : List Job := t7_683jobs0




def t7_684root : Job := ⟨plan8546,[],none,⟨21,6,0⟩⟩
def t7_684jobs0 : List Job := [⟨plan8546,[],none,⟨21,6,0⟩⟩]

def t7_684jobs : List Job := t7_684jobs0




def t7_685root : Job := ⟨plan8705,[],none,⟨21,10,0⟩⟩
def t7_685jobs0 : List Job := [⟨plan8705,[],none,⟨21,10,0⟩⟩]

def t7_685jobs : List Job := t7_685jobs0




def t7_686root : Job := ⟨plan8706,[],none,⟨21,10,0⟩⟩
def t7_686jobs0 : List Job := [⟨plan8706,[],none,⟨21,10,0⟩⟩]

def t7_686jobs : List Job := t7_686jobs0




def t7_687root : Job := ⟨plan8707,[],none,⟨21,10,0⟩⟩
def t7_687jobs0 : List Job := [⟨plan8707,[],none,⟨21,10,0⟩⟩]

def t7_687jobs : List Job := t7_687jobs0




def t7_688root : Job := ⟨plan8936,[],none,⟨21,15,0⟩⟩
def t7_688jobs0 : List Job := [⟨plan8936,[],none,⟨21,15,0⟩⟩]

def t7_688jobs : List Job := t7_688jobs0




def t7_689root : Job := ⟨plan8937,[],none,⟨21,15,0⟩⟩
def t7_689jobs0 : List Job := [⟨plan8937,[],none,⟨21,15,0⟩⟩]

def t7_689jobs : List Job := t7_689jobs0




def t7_690root : Job := ⟨plan8938,[],none,⟨21,15,0⟩⟩
def t7_690jobs0 : List Job := [⟨plan8938,[],none,⟨21,15,0⟩⟩]

def t7_690jobs : List Job := t7_690jobs0




def t7_691root : Job := ⟨plan8939,[],none,⟨21,15,0⟩⟩
def t7_691jobs0 : List Job := [⟨plan8939,[],none,⟨21,15,0⟩⟩]

def t7_691jobs : List Job := t7_691jobs0




def t7_692root : Job := ⟨plan8940,[],none,⟨21,15,0⟩⟩
def t7_692jobs0 : List Job := [⟨plan8940,[],none,⟨21,15,0⟩⟩]

def t7_692jobs : List Job := t7_692jobs0




def t7_693root : Job := ⟨plan8941,[],none,⟨21,15,0⟩⟩
def t7_693jobs0 : List Job := [⟨plan8941,[],none,⟨21,15,0⟩⟩]

def t7_693jobs : List Job := t7_693jobs0




def t7_694root : Job := ⟨plan9107,[],none,⟨21,21,0⟩⟩
def t7_694jobs0 : List Job := [⟨plan9107,[],none,⟨21,21,0⟩⟩]

def t7_694jobs : List Job := t7_694jobs0




def t7_695root : Job := ⟨plan9108,[],none,⟨21,21,0⟩⟩
def t7_695jobs0 : List Job := [⟨plan9108,[],none,⟨21,21,0⟩⟩]

def t7_695jobs : List Job := t7_695jobs0




def t7_696root : Job := ⟨plan9109,[],none,⟨21,21,0⟩⟩
def t7_696jobs0 : List Job := [⟨plan9109,[],none,⟨21,21,0⟩⟩]

def t7_696jobs : List Job := t7_696jobs0




def t7_697root : Job := ⟨plan9110,[],none,⟨21,21,0⟩⟩
def t7_697jobs0 : List Job := [⟨plan9110,[],none,⟨21,21,0⟩⟩]

def t7_697jobs : List Job := t7_697jobs0




def t7_698root : Job := ⟨plan9111,[],none,⟨21,21,0⟩⟩
def t7_698jobs0 : List Job := [⟨plan9111,[],none,⟨21,21,0⟩⟩]

def t7_698jobs : List Job := t7_698jobs0




def t7_699root : Job := ⟨plan9112,[],none,⟨21,21,0⟩⟩
def t7_699jobs0 : List Job := [⟨plan9112,[],none,⟨21,21,0⟩⟩]

def t7_699jobs : List Job := t7_699jobs0




def t7_700root : Job := ⟨plan9113,[],none,⟨21,21,0⟩⟩
def t7_700jobs0 : List Job := [⟨plan9113,[],none,⟨21,21,0⟩⟩]

def t7_700jobs : List Job := t7_700jobs0




def t7_701root : Job := ⟨plan8942,[],none,⟨21,15,0⟩⟩
def t7_701jobs0 : List Job := [⟨plan8942,[],none,⟨21,15,0⟩⟩]

def t7_701jobs : List Job := t7_701jobs0




def t7_702root : Job := ⟨plan9114,[],none,⟨21,21,0⟩⟩
def t7_702jobs0 : List Job := [⟨plan9114,[],none,⟨21,21,0⟩⟩]

def t7_702jobs : List Job := t7_702jobs0




def t7_703root : Job := ⟨plan9115,[],none,⟨21,21,0⟩⟩
def t7_703jobs0 : List Job := [⟨plan9115,[],none,⟨21,21,0⟩⟩]

def t7_703jobs : List Job := t7_703jobs0




def t7_704root : Job := ⟨plan9116,[],none,⟨21,21,0⟩⟩
def t7_704jobs0 : List Job := [⟨plan9116,[],none,⟨21,21,0⟩⟩]

def t7_704jobs : List Job := t7_704jobs0




def t7_705root : Job := ⟨plan9117,[],none,⟨21,21,0⟩⟩
def t7_705jobs0 : List Job := [⟨plan9117,[],none,⟨21,21,0⟩⟩]

def t7_705jobs : List Job := t7_705jobs0




def t7_706root : Job := ⟨plan9118,[],none,⟨21,21,0⟩⟩
def t7_706jobs0 : List Job := [⟨plan9118,[],none,⟨21,21,0⟩⟩]

def t7_706jobs : List Job := t7_706jobs0




def t7_707root : Job := ⟨plan9119,[],none,⟨21,21,0⟩⟩
def t7_707jobs0 : List Job := [⟨plan9119,[],none,⟨21,21,0⟩⟩]

def t7_707jobs : List Job := t7_707jobs0




def t7_708root : Job := ⟨plan9120,[],none,⟨21,21,0⟩⟩
def t7_708jobs0 : List Job := [⟨plan9120,[],none,⟨21,21,0⟩⟩]

def t7_708jobs : List Job := t7_708jobs0




def t7_709root : Job := ⟨plan9121,[],none,⟨21,21,0⟩⟩
def t7_709jobs0 : List Job := [⟨plan9121,[],none,⟨21,21,0⟩⟩]

def t7_709jobs : List Job := t7_709jobs0




def t7_710root : Job := ⟨plan9122,[],none,⟨21,21,0⟩⟩
def t7_710jobs0 : List Job := [⟨plan9122,[],none,⟨21,21,0⟩⟩]

def t7_710jobs : List Job := t7_710jobs0




def t7_711root : Job := ⟨plan9123,[],none,⟨21,21,0⟩⟩
def t7_711jobs0 : List Job := [⟨plan9123,[],none,⟨21,21,0⟩⟩]

def t7_711jobs : List Job := t7_711jobs0




def t7_712root : Job := ⟨plan9124,[],none,⟨21,21,0⟩⟩
def t7_712jobs0 : List Job := [⟨plan9124,[],none,⟨21,21,0⟩⟩]

def t7_712jobs : List Job := t7_712jobs0




def t7_713root : Job := ⟨plan9125,[],none,⟨21,21,0⟩⟩
def t7_713jobs0 : List Job := [⟨plan9125,[],none,⟨21,21,0⟩⟩]

def t7_713jobs : List Job := t7_713jobs0




def t7_714root : Job := ⟨plan9126,[],none,⟨21,21,0⟩⟩
def t7_714jobs0 : List Job := [⟨plan9126,[],none,⟨21,21,0⟩⟩]

def t7_714jobs : List Job := t7_714jobs0




def t7_715root : Job := ⟨plan9127,[],none,⟨21,21,0⟩⟩
def t7_715jobs0 : List Job := [⟨plan9127,[],none,⟨21,21,0⟩⟩]

def t7_715jobs : List Job := t7_715jobs0




def t7_716root : Job := ⟨plan9128,[],none,⟨21,21,0⟩⟩
def t7_716jobs0 : List Job := [⟨plan9128,[],none,⟨21,21,0⟩⟩]

def t7_716jobs : List Job := t7_716jobs0




def t7_717root : Job := ⟨plan9129,[],none,⟨21,21,0⟩⟩
def t7_717jobs0 : List Job := [⟨plan9129,[],none,⟨21,21,0⟩⟩]

def t7_717jobs : List Job := t7_717jobs0




def t7_718root : Job := ⟨plan9130,[],none,⟨21,21,0⟩⟩
def t7_718jobs0 : List Job := [⟨plan9130,[],none,⟨21,21,0⟩⟩]

def t7_718jobs : List Job := t7_718jobs0




def t7_719root : Job := ⟨plan9131,[],none,⟨21,21,0⟩⟩
def t7_719jobs0 : List Job := [⟨plan9131,[],none,⟨21,21,0⟩⟩]

def t7_719jobs : List Job := t7_719jobs0




def t8_0root : Job := ⟨plan9190,[],none,⟨28,21,0⟩⟩
def t8_0jobs0 : List Job := [⟨plan9190,[],none,⟨28,21,0⟩⟩]

def t8_0jobs : List Job := t8_0jobs0




def t8_1root : Job := ⟨plan9177,[],none,⟨28,15,0⟩⟩
def t8_1jobs0 : List Job := [⟨plan9177,[],none,⟨28,15,0⟩⟩]

def t8_1jobs : List Job := t8_1jobs0




def t8_2root : Job := ⟨plan9191,[],none,⟨28,21,0⟩⟩
def t8_2jobs0 : List Job := [⟨plan9191,[],none,⟨28,21,0⟩⟩]

def t8_2jobs : List Job := t8_2jobs0




def t8_3root : Job := ⟨plan9192,[],none,⟨28,21,0⟩⟩
def t8_3jobs0 : List Job := [⟨plan9192,[],none,⟨28,21,0⟩⟩]

def t8_3jobs : List Job := t8_3jobs0




def t8_4root : Job := ⟨plan9193,[],none,⟨28,21,0⟩⟩
def t8_4jobs0 : List Job := [⟨plan9193,[],none,⟨28,21,0⟩⟩]

def t8_4jobs : List Job := t8_4jobs0




def t8_5root : Job := ⟨plan9178,[],none,⟨28,15,0⟩⟩
def t8_5jobs0 : List Job := [⟨plan9178,[],none,⟨28,15,0⟩⟩]

def t8_5jobs : List Job := t8_5jobs0




def t8_6root : Job := ⟨plan9173,[],none,⟨28,10,0⟩⟩
def t8_6jobs0 : List Job := [⟨plan9173,[],none,⟨28,10,0⟩⟩]

def t8_6jobs : List Job := t8_6jobs0




def t8_7root : Job := ⟨plan9179,[],none,⟨28,15,0⟩⟩
def t8_7jobs0 : List Job := [⟨plan9179,[],none,⟨28,15,0⟩⟩]

def t8_7jobs : List Job := t8_7jobs0




def t8_8root : Job := ⟨plan9180,[],none,⟨28,15,0⟩⟩
def t8_8jobs0 : List Job := [⟨plan9180,[],none,⟨28,15,0⟩⟩]

def t8_8jobs : List Job := t8_8jobs0




def t8_9root : Job := ⟨plan9181,[],none,⟨28,15,0⟩⟩
def t8_9jobs0 : List Job := [⟨plan9181,[],none,⟨28,15,0⟩⟩]

def t8_9jobs : List Job := t8_9jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


