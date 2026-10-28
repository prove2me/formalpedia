-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks041
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks041
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:24:40.11374+00:00
-- url     : https://prove2.me/theorems/7db1ee3b-ff3f-45be-a794-bc73865faa22
-- title:
--   Endpoint22 Reach Checks041 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks041 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t5_1411root`, `ThreeBoundEndpoint22Reachable.t5_1411jobs0`, `ThreeBoundEndpoint22Reachable.t5_1411jobs`, `ThreeBoundEndpoint22Reachable.t5_1412root`, `ThreeBoundEndpoint22Reachable.t5_1412jobs0`, `ThreeBoundEndpoint22Reachable.t5_1412jobs`, `ThreeBoundEndpoint22Reachable.t5_1413root`, `ThreeBoundEndpoint22Reachable.t5_1413jobs0`, `ThreeBoundEndpoint22Reachable.t5_1413jobs`, `ThreeBoundEndpoint22Reachable.t5_1414root`, `ThreeBoundEndpoint22Reachable.t5_1414jobs0`, `ThreeBoundEndpoint22Reachable.t5_1414jobs`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks041.lean, lines 1–413.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans039
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans041
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans045
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans046
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans051
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

def t5_1398root : Job := ⟨plan4411,[],none,⟨10,3,0⟩⟩
def t5_1398jobs0 : List Job := [⟨plan4411,[],none,⟨10,3,0⟩⟩]

def t5_1398jobs : List Job := t5_1398jobs0




def t5_1399root : Job := ⟨plan4899,[],none,⟨10,6,0⟩⟩
def t5_1399jobs0 : List Job := [⟨plan4899,[],none,⟨10,6,0⟩⟩]

def t5_1399jobs : List Job := t5_1399jobs0




def t5_1400root : Job := ⟨plan4900,[],none,⟨10,6,0⟩⟩
def t5_1400jobs0 : List Job := [⟨plan4900,[],none,⟨10,6,0⟩⟩]

def t5_1400jobs : List Job := t5_1400jobs0




def t5_1401root : Job := ⟨plan4901,[],none,⟨10,6,0⟩⟩
def t5_1401jobs0 : List Job := [⟨plan4901,[],none,⟨10,6,0⟩⟩]

def t5_1401jobs : List Job := t5_1401jobs0




def t5_1402root : Job := ⟨plan4902,[],none,⟨10,6,0⟩⟩
def t5_1402jobs0 : List Job := [⟨plan4902,[],none,⟨10,6,0⟩⟩]

def t5_1402jobs : List Job := t5_1402jobs0




def t5_1403root : Job := ⟨plan4903,[],none,⟨10,6,0⟩⟩
def t5_1403jobs0 : List Job := [⟨plan4903,[],none,⟨10,6,0⟩⟩]

def t5_1403jobs : List Job := t5_1403jobs0




def t5_1404root : Job := ⟨plan4904,[],none,⟨10,6,0⟩⟩
def t5_1404jobs0 : List Job := [⟨plan4904,[],none,⟨10,6,0⟩⟩]

def t5_1404jobs : List Job := t5_1404jobs0




def t5_1405root : Job := ⟨plan4905,[],none,⟨10,6,0⟩⟩
def t5_1405jobs0 : List Job := [⟨plan4905,[],none,⟨10,6,0⟩⟩]

def t5_1405jobs : List Job := t5_1405jobs0




def t5_1406root : Job := ⟨plan4906,[],none,⟨10,6,0⟩⟩
def t5_1406jobs0 : List Job := [⟨plan4906,[],none,⟨10,6,0⟩⟩]

def t5_1406jobs : List Job := t5_1406jobs0




def t5_1407root : Job := ⟨plan4907,[],none,⟨10,6,0⟩⟩
def t5_1407jobs0 : List Job := [⟨plan4907,[],none,⟨10,6,0⟩⟩]

def t5_1407jobs : List Job := t5_1407jobs0




def t5_1408root : Job := ⟨plan4908,[],none,⟨10,6,0⟩⟩
def t5_1408jobs0 : List Job := [⟨plan4908,[],none,⟨10,6,0⟩⟩]

def t5_1408jobs : List Job := t5_1408jobs0




def t5_1409root : Job := ⟨plan4909,[],none,⟨10,6,0⟩⟩
def t5_1409jobs0 : List Job := [⟨plan4909,[],none,⟨10,6,0⟩⟩]

def t5_1409jobs : List Job := t5_1409jobs0




def t5_1410root : Job := ⟨plan4910,[],none,⟨10,6,0⟩⟩
def t5_1410jobs0 : List Job := [⟨plan4910,[],none,⟨10,6,0⟩⟩]

def t5_1410jobs : List Job := t5_1410jobs0




def t5_1411root : Job := ⟨plan3988,[],none,⟨10,1,0⟩⟩
def t5_1411jobs0 : List Job := [⟨plan3988,[],none,⟨10,1,0⟩⟩]

def t5_1411jobs : List Job := t5_1411jobs0




def t5_1412root : Job := ⟨plan4412,[],none,⟨10,3,0⟩⟩
def t5_1412jobs0 : List Job := [⟨plan4412,[],none,⟨10,3,0⟩⟩]

def t5_1412jobs : List Job := t5_1412jobs0




def t5_1413root : Job := ⟨plan4413,[],none,⟨10,3,0⟩⟩
def t5_1413jobs0 : List Job := [⟨plan4413,[],none,⟨10,3,0⟩⟩]

def t5_1413jobs : List Job := t5_1413jobs0




def t5_1414root : Job := ⟨plan4414,[],none,⟨10,3,0⟩⟩
def t5_1414jobs0 : List Job := [⟨plan4414,[],none,⟨10,3,0⟩⟩]

def t5_1414jobs : List Job := t5_1414jobs0




def t5_1415root : Job := ⟨plan4911,[],none,⟨10,6,0⟩⟩
def t5_1415jobs0 : List Job := [⟨plan4911,[],none,⟨10,6,0⟩⟩]

def t5_1415jobs : List Job := t5_1415jobs0




def t5_1416root : Job := ⟨plan4912,[],none,⟨10,6,0⟩⟩
def t5_1416jobs0 : List Job := [⟨plan4912,[],none,⟨10,6,0⟩⟩]

def t5_1416jobs : List Job := t5_1416jobs0




def t5_1417root : Job := ⟨plan4913,[],none,⟨10,6,0⟩⟩
def t5_1417jobs0 : List Job := [⟨plan4913,[],none,⟨10,6,0⟩⟩]

def t5_1417jobs : List Job := t5_1417jobs0




def t5_1418root : Job := ⟨plan4914,[],none,⟨10,6,0⟩⟩
def t5_1418jobs0 : List Job := [⟨plan4914,[],none,⟨10,6,0⟩⟩]

def t5_1418jobs : List Job := t5_1418jobs0




def t5_1419root : Job := ⟨plan4415,[],none,⟨10,3,0⟩⟩
def t5_1419jobs0 : List Job := [⟨plan4415,[],none,⟨10,3,0⟩⟩]

def t5_1419jobs : List Job := t5_1419jobs0




def t5_1420root : Job := ⟨plan4915,[],none,⟨10,6,0⟩⟩
def t5_1420jobs0 : List Job := [⟨plan4915,[],none,⟨10,6,0⟩⟩]

def t5_1420jobs : List Job := t5_1420jobs0




def t5_1421root : Job := ⟨plan4916,[],none,⟨10,6,0⟩⟩
def t5_1421jobs0 : List Job := [⟨plan4916,[],none,⟨10,6,0⟩⟩]

def t5_1421jobs : List Job := t5_1421jobs0




def t5_1422root : Job := ⟨plan4917,[],none,⟨10,6,0⟩⟩
def t5_1422jobs0 : List Job := [⟨plan4917,[],none,⟨10,6,0⟩⟩]

def t5_1422jobs : List Job := t5_1422jobs0




def t5_1423root : Job := ⟨plan4918,[],none,⟨10,6,0⟩⟩
def t5_1423jobs0 : List Job := [⟨plan4918,[],none,⟨10,6,0⟩⟩]

def t5_1423jobs : List Job := t5_1423jobs0




def t5_1424root : Job := ⟨plan4919,[],none,⟨10,6,0⟩⟩
def t5_1424jobs0 : List Job := [⟨plan4919,[],none,⟨10,6,0⟩⟩]

def t5_1424jobs : List Job := t5_1424jobs0




def t5_1425root : Job := ⟨plan4920,[],none,⟨10,6,0⟩⟩
def t5_1425jobs0 : List Job := [⟨plan4920,[],none,⟨10,6,0⟩⟩]

def t5_1425jobs : List Job := t5_1425jobs0




def t5_1426root : Job := ⟨plan4921,[],none,⟨10,6,0⟩⟩
def t5_1426jobs0 : List Job := [⟨plan4921,[],none,⟨10,6,0⟩⟩]

def t5_1426jobs : List Job := t5_1426jobs0




def t5_1427root : Job := ⟨plan4922,[],none,⟨10,6,0⟩⟩
def t5_1427jobs0 : List Job := [⟨plan4922,[],none,⟨10,6,0⟩⟩]

def t5_1427jobs : List Job := t5_1427jobs0




def t5_1428root : Job := ⟨plan3757,[],none,⟨10,0,0⟩⟩
def t5_1428jobs0 : List Job := [⟨plan3757,[],none,⟨10,0,0⟩⟩]

def t5_1428jobs : List Job := t5_1428jobs0




def t5_1429root : Job := ⟨plan3989,[],none,⟨10,1,0⟩⟩
def t5_1429jobs0 : List Job := [⟨plan3989,[],none,⟨10,1,0⟩⟩]

def t5_1429jobs : List Job := t5_1429jobs0




def t5_1430root : Job := ⟨plan3990,[],none,⟨10,1,0⟩⟩
def t5_1430jobs0 : List Job := [⟨plan3990,[],none,⟨10,1,0⟩⟩]

def t5_1430jobs : List Job := t5_1430jobs0




def t5_1431root : Job := ⟨plan3991,[],none,⟨10,1,0⟩⟩
def t5_1431jobs0 : List Job := [⟨plan3991,[],none,⟨10,1,0⟩⟩]

def t5_1431jobs : List Job := t5_1431jobs0




def t5_1432root : Job := ⟨plan4416,[],none,⟨10,3,0⟩⟩
def t5_1432jobs0 : List Job := [⟨plan4416,[],none,⟨10,3,0⟩⟩]

def t5_1432jobs : List Job := t5_1432jobs0




def t5_1433root : Job := ⟨plan4417,[],none,⟨10,3,0⟩⟩
def t5_1433jobs0 : List Job := [⟨plan2763,[⟨8,0,2⟩],(some ⟨8,0,2⟩),⟨10,1,(-2)⟩⟩,⟨plan2763,[⟨8,1,1⟩],(some ⟨8,1,1⟩),⟨9,2,0⟩⟩]

def t5_1433jobs1 : List Job := [⟨plan2763,[⟨8,1,2⟩],(some ⟨8,1,2⟩),⟨9,1,(-1)⟩⟩]

def t5_1433jobs : List Job := t5_1433jobs0++t5_1433jobs1



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


