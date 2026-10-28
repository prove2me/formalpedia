-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks139
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks139
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:31:13.978587+00:00
-- url     : https://prove2.me/theorems/f2effd5a-8e31-4281-8256-ae9e0c2e684a
-- title:
--   Endpoint22 Reach Checks139 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks139 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t6_1447jobs`, `ThreeBoundEndpoint22Reachable.t6_1448root`, `ThreeBoundEndpoint22Reachable.t6_1448jobs0`, `ThreeBoundEndpoint22Reachable.t6_1448jobs`, `ThreeBoundEndpoint22Reachable.t6_1449root`, `ThreeBoundEndpoint22Reachable.t6_1449jobs0`, `ThreeBoundEndpoint22Reachable.t6_1449jobs`, `ThreeBoundEndpoint22Reachable.t6_1450root`, `ThreeBoundEndpoint22Reachable.t6_1450jobs0`, `ThreeBoundEndpoint22Reachable.t6_1450jobs`, `ThreeBoundEndpoint22Reachable.t6_1451root`, `ThreeBoundEndpoint22Reachable.t6_1451jobs0`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks139.lean, lines 1–335.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans069
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans073
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans079
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

def t6_1438root : Job := ⟨plan7086,[],none,⟨15,6,0⟩⟩
def t6_1438jobs0 : List Job := [⟨plan5566,[⟨8,0,3⟩],(some ⟨8,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5566,[⟨8,1,2⟩],(some ⟨8,1,2⟩),⟨14,4,(-1)⟩⟩]

def t6_1438jobs1 : List Job := [⟨plan5566,[⟨8,1,3⟩],(some ⟨8,1,3⟩),⟨14,3,(-2)⟩⟩]

def t6_1438jobs : List Job := t6_1438jobs0++t6_1438jobs1




def t6_1439root : Job := ⟨plan7087,[],none,⟨15,6,0⟩⟩
def t6_1439jobs0 : List Job := [⟨plan7087,[],none,⟨15,6,0⟩⟩]

def t6_1439jobs : List Job := t6_1439jobs0




def t6_1440root : Job := ⟨plan7088,[],none,⟨15,6,0⟩⟩
def t6_1440jobs0 : List Job := [⟨plan5568,[⟨8,0,3⟩],(some ⟨8,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5568,[⟨8,1,2⟩],(some ⟨8,1,2⟩),⟨14,4,(-1)⟩⟩]

def t6_1440jobs1 : List Job := [⟨plan5568,[⟨8,1,3⟩],(some ⟨8,1,3⟩),⟨14,3,(-2)⟩⟩]

def t6_1440jobs : List Job := t6_1440jobs0++t6_1440jobs1




def t6_1441root : Job := ⟨plan7089,[],none,⟨15,6,0⟩⟩
def t6_1441jobs0 : List Job := [⟨plan3367,[⟨8,0,3⟩,⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨15,3,(-7)⟩⟩,⟨plan3367,[⟨8,0,3⟩,⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨14,3,(-6)⟩⟩,⟨plan3367,[⟨8,0,3⟩,⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨14,3,(-7)⟩⟩,⟨plan3367,[⟨8,0,3⟩,⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨13,3,(-5)⟩⟩,⟨plan3367,[⟨8,0,3⟩,⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨13,3,(-6)⟩⟩,⟨plan3367,[⟨8,1,2⟩,⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨14,4,(-5)⟩⟩,⟨plan3367,[⟨8,1,2⟩,⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨13,4,(-4)⟩⟩,⟨plan3367,[⟨8,1,2⟩,⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨13,4,(-5)⟩⟩,⟨plan3367,[⟨8,1,2⟩,⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨12,4,(-3)⟩⟩]

def t6_1441jobs1 : List Job := [⟨plan3367,[⟨8,1,2⟩,⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨12,4,(-4)⟩⟩,⟨plan3367,[⟨8,1,3⟩,⟨2,0,4⟩],(some ⟨2,0,4⟩),⟨14,3,(-6)⟩⟩,⟨plan3367,[⟨8,1,3⟩,⟨2,1,3⟩],(some ⟨2,1,3⟩),⟨13,3,(-5)⟩⟩,⟨plan3367,[⟨8,1,3⟩,⟨2,1,4⟩],(some ⟨2,1,4⟩),⟨13,3,(-6)⟩⟩,⟨plan3367,[⟨8,1,3⟩,⟨2,2,2⟩],(some ⟨2,2,2⟩),⟨12,3,(-4)⟩⟩]

def t6_1441jobs2 : List Job := [⟨plan3367,[⟨8,1,3⟩,⟨2,2,3⟩],(some ⟨2,2,3⟩),⟨12,3,(-5)⟩⟩]

def t6_1441jobs : List Job := t6_1441jobs0++t6_1441jobs1++t6_1441jobs2




def t6_1442root : Job := ⟨plan7090,[],none,⟨15,6,0⟩⟩
def t6_1442jobs0 : List Job := [⟨plan5570,[⟨8,0,3⟩],(some ⟨8,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5570,[⟨8,1,2⟩],(some ⟨8,1,2⟩),⟨14,4,(-1)⟩⟩]

def t6_1442jobs1 : List Job := [⟨plan5570,[⟨8,1,3⟩],(some ⟨8,1,3⟩),⟨14,3,(-2)⟩⟩]

def t6_1442jobs : List Job := t6_1442jobs0++t6_1442jobs1




def t6_1443root : Job := ⟨plan7091,[],none,⟨15,6,0⟩⟩
def t6_1443jobs0 : List Job := [⟨plan7091,[],none,⟨15,6,0⟩⟩]

def t6_1443jobs : List Job := t6_1443jobs0




def t6_1444root : Job := ⟨plan6669,[],none,⟨15,3,0⟩⟩
def t6_1444jobs0 : List Job := [⟨plan6669,[],none,⟨15,3,0⟩⟩]

def t6_1444jobs : List Job := t6_1444jobs0




def t6_1445root : Job := ⟨plan7092,[],none,⟨15,6,0⟩⟩
def t6_1445jobs0 : List Job := [⟨plan7092,[],none,⟨15,6,0⟩⟩]

def t6_1445jobs : List Job := t6_1445jobs0




def t6_1446root : Job := ⟨plan7093,[],none,⟨15,6,0⟩⟩
def t6_1446jobs0 : List Job := [⟨plan5573,[⟨8,0,3⟩],(some ⟨8,0,3⟩),⟨15,3,(-3)⟩⟩,⟨plan5573,[⟨8,1,2⟩],(some ⟨8,1,2⟩),⟨14,4,(-1)⟩⟩]

def t6_1446jobs1 : List Job := [⟨plan5573,[⟨8,1,3⟩],(some ⟨8,1,3⟩),⟨14,3,(-2)⟩⟩]

def t6_1446jobs : List Job := t6_1446jobs0++t6_1446jobs1




def t6_1447root : Job := ⟨plan7094,[],none,⟨15,6,0⟩⟩
def t6_1447jobs0 : List Job := [⟨plan7094,[],none,⟨15,6,0⟩⟩]

def t6_1447jobs : List Job := t6_1447jobs0




def t6_1448root : Job := ⟨plan7587,[],none,⟨15,10,0⟩⟩
def t6_1448jobs0 : List Job := [⟨plan7587,[],none,⟨15,10,0⟩⟩]

def t6_1448jobs : List Job := t6_1448jobs0




def t6_1449root : Job := ⟨plan7588,[],none,⟨15,10,0⟩⟩
def t6_1449jobs0 : List Job := [⟨plan7588,[],none,⟨15,10,0⟩⟩]

def t6_1449jobs : List Job := t6_1449jobs0




def t6_1450root : Job := ⟨plan7589,[],none,⟨15,10,0⟩⟩
def t6_1450jobs0 : List Job := [⟨plan7589,[],none,⟨15,10,0⟩⟩]

def t6_1450jobs : List Job := t6_1450jobs0




def t6_1451root : Job := ⟨plan7590,[],none,⟨15,10,0⟩⟩
def t6_1451jobs0 : List Job := [⟨plan7590,[],none,⟨15,10,0⟩⟩]

def t6_1451jobs : List Job := t6_1451jobs0




def t6_1452root : Job := ⟨plan7591,[],none,⟨15,10,0⟩⟩
def t6_1452jobs0 : List Job := [⟨plan7591,[],none,⟨15,10,0⟩⟩]

def t6_1452jobs : List Job := t6_1452jobs0




def t6_1453root : Job := ⟨plan7592,[],none,⟨15,10,0⟩⟩
def t6_1453jobs0 : List Job := [⟨plan7592,[],none,⟨15,10,0⟩⟩]

def t6_1453jobs : List Job := t6_1453jobs0




def t6_1454root : Job := ⟨plan7593,[],none,⟨15,10,0⟩⟩
def t6_1454jobs0 : List Job := [⟨plan7593,[],none,⟨15,10,0⟩⟩]

def t6_1454jobs : List Job := t6_1454jobs0




def t6_1455root : Job := ⟨plan7594,[],none,⟨15,10,0⟩⟩
def t6_1455jobs0 : List Job := [⟨plan7594,[],none,⟨15,10,0⟩⟩]

def t6_1455jobs : List Job := t6_1455jobs0




def t6_1456root : Job := ⟨plan7595,[],none,⟨15,10,0⟩⟩
def t6_1456jobs0 : List Job := [⟨plan7595,[],none,⟨15,10,0⟩⟩]

def t6_1456jobs : List Job := t6_1456jobs0




def t6_1457root : Job := ⟨plan7596,[],none,⟨15,10,0⟩⟩
def t6_1457jobs0 : List Job := [⟨plan7596,[],none,⟨15,10,0⟩⟩]

def t6_1457jobs : List Job := t6_1457jobs0




def t6_1458root : Job := ⟨plan7597,[],none,⟨15,10,0⟩⟩
def t6_1458jobs0 : List Job := [⟨plan7597,[],none,⟨15,10,0⟩⟩]

def t6_1458jobs : List Job := t6_1458jobs0




def t6_1459root : Job := ⟨plan7598,[],none,⟨15,10,0⟩⟩
def t6_1459jobs0 : List Job := [⟨plan7598,[],none,⟨15,10,0⟩⟩]

def t6_1459jobs : List Job := t6_1459jobs0




def t6_1460root : Job := ⟨plan7599,[],none,⟨15,10,0⟩⟩
def t6_1460jobs0 : List Job := [⟨plan7599,[],none,⟨15,10,0⟩⟩]

def t6_1460jobs : List Job := t6_1460jobs0




def t6_1461root : Job := ⟨plan7600,[],none,⟨15,10,0⟩⟩
def t6_1461jobs0 : List Job := [⟨plan7600,[],none,⟨15,10,0⟩⟩]

def t6_1461jobs : List Job := t6_1461jobs0




def t6_1462root : Job := ⟨plan7601,[],none,⟨15,10,0⟩⟩
def t6_1462jobs0 : List Job := [⟨plan7601,[],none,⟨15,10,0⟩⟩]

def t6_1462jobs : List Job := t6_1462jobs0




def t6_1463root : Job := ⟨plan7602,[],none,⟨15,10,0⟩⟩
def t6_1463jobs0 : List Job := [⟨plan5755,[⟨8,0,4⟩],(some ⟨8,0,4⟩),⟨15,6,(-4)⟩⟩,⟨plan5755,[⟨8,1,3⟩],(some ⟨8,1,3⟩),⟨14,7,(-2)⟩⟩]

def t6_1463jobs1 : List Job := [⟨plan5755,[⟨8,1,4⟩],(some ⟨8,1,4⟩),⟨14,6,(-3)⟩⟩]

def t6_1463jobs : List Job := t6_1463jobs0++t6_1463jobs1




def t6_1464root : Job := ⟨plan7603,[],none,⟨15,10,0⟩⟩
def t6_1464jobs0 : List Job := [⟨plan7603,[],none,⟨15,10,0⟩⟩]

def t6_1464jobs : List Job := t6_1464jobs0




def t6_1465root : Job := ⟨plan7604,[],none,⟨15,10,0⟩⟩
def t6_1465jobs0 : List Job := [⟨plan7604,[],none,⟨15,10,0⟩⟩]

def t6_1465jobs : List Job := t6_1465jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


