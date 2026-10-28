-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks042
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks042
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:24:23.537475+00:00
-- url     : https://prove2.me/theorems/ec74f759-4082-4b5b-a6cb-dbd49ec977ec
-- title:
--   Endpoint22 Reach Checks042 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks042 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t5_1445jobs1`, `ThreeBoundEndpoint22Reachable.t5_1445jobs`, `ThreeBoundEndpoint22Reachable.t5_1446root`, `ThreeBoundEndpoint22Reachable.t5_1446jobs0`, `ThreeBoundEndpoint22Reachable.t5_1446jobs`, `ThreeBoundEndpoint22Reachable.t5_1447root`, `ThreeBoundEndpoint22Reachable.t5_1447jobs0`, `ThreeBoundEndpoint22Reachable.t5_1447jobs`, `ThreeBoundEndpoint22Reachable.t5_1448root`, `ThreeBoundEndpoint22Reachable.t5_1448jobs0`, `ThreeBoundEndpoint22Reachable.t5_1435root`, `ThreeBoundEndpoint22Reachable.t5_1448jobs`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks042.lean, lines 1–243.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans041
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

def t5_1434root : Job := ⟨plan4418,[],none,⟨10,3,0⟩⟩
def t5_1434jobs0 : List Job := [⟨plan4418,[],none,⟨10,3,0⟩⟩]

def t5_1434jobs : List Job := t5_1434jobs0




def t5_1435root : Job := ⟨plan4419,[],none,⟨10,3,0⟩⟩
def t5_1435jobs0 : List Job := [⟨plan4419,[],none,⟨10,3,0⟩⟩]

def t5_1435jobs : List Job := t5_1435jobs0




def t5_1436root : Job := ⟨plan4420,[],none,⟨10,3,0⟩⟩
def t5_1436jobs0 : List Job := [⟨plan2766,[⟨8,0,2⟩],(some ⟨8,0,2⟩),⟨10,1,(-2)⟩⟩,⟨plan2766,[⟨8,1,1⟩],(some ⟨8,1,1⟩),⟨9,2,0⟩⟩]

def t5_1436jobs1 : List Job := [⟨plan2766,[⟨8,1,2⟩],(some ⟨8,1,2⟩),⟨9,1,(-1)⟩⟩]

def t5_1436jobs : List Job := t5_1436jobs0++t5_1436jobs1




def t5_1437root : Job := ⟨plan4421,[],none,⟨10,3,0⟩⟩
def t5_1437jobs0 : List Job := [⟨plan4421,[],none,⟨10,3,0⟩⟩]

def t5_1437jobs : List Job := t5_1437jobs0




def t5_1438root : Job := ⟨plan4923,[],none,⟨10,6,0⟩⟩
def t5_1438jobs0 : List Job := [⟨plan4923,[],none,⟨10,6,0⟩⟩]

def t5_1438jobs : List Job := t5_1438jobs0




def t5_1439root : Job := ⟨plan4924,[],none,⟨10,6,0⟩⟩
def t5_1439jobs0 : List Job := [⟨plan4924,[],none,⟨10,6,0⟩⟩]

def t5_1439jobs : List Job := t5_1439jobs0




def t5_1440root : Job := ⟨plan4925,[],none,⟨10,6,0⟩⟩
def t5_1440jobs0 : List Job := [⟨plan4925,[],none,⟨10,6,0⟩⟩]

def t5_1440jobs : List Job := t5_1440jobs0




def t5_1441root : Job := ⟨plan4926,[],none,⟨10,6,0⟩⟩
def t5_1441jobs0 : List Job := [⟨plan2907,[⟨8,0,3⟩],(some ⟨8,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2907,[⟨8,1,2⟩],(some ⟨8,1,2⟩),⟨9,4,(-1)⟩⟩]

def t5_1441jobs1 : List Job := [⟨plan2907,[⟨8,1,3⟩],(some ⟨8,1,3⟩),⟨9,3,(-2)⟩⟩]

def t5_1441jobs : List Job := t5_1441jobs0++t5_1441jobs1




def t5_1442root : Job := ⟨plan4927,[],none,⟨10,6,0⟩⟩
def t5_1442jobs0 : List Job := [⟨plan2908,[⟨8,0,3⟩],(some ⟨8,0,3⟩),⟨10,3,(-3)⟩⟩]

def t5_1442jobs1 : List Job := [⟨plan2908,[⟨8,1,2⟩],(some ⟨8,1,2⟩),⟨9,4,(-1)⟩⟩]

def t5_1442jobs2 : List Job := [⟨plan2908,[⟨8,1,3⟩],(some ⟨8,1,3⟩),⟨9,3,(-2)⟩⟩]

def t5_1442jobs : List Job := t5_1442jobs0++t5_1442jobs1++t5_1442jobs2




def t5_1443root : Job := ⟨plan4928,[],none,⟨10,6,0⟩⟩
def t5_1443jobs0 : List Job := [⟨plan4928,[],none,⟨10,6,0⟩⟩]

def t5_1443jobs : List Job := t5_1443jobs0




def t5_1444root : Job := ⟨plan4929,[],none,⟨10,6,0⟩⟩
def t5_1444jobs0 : List Job := [⟨plan4929,[],none,⟨10,6,0⟩⟩]

def t5_1444jobs : List Job := t5_1444jobs0




def t5_1445root : Job := ⟨plan4930,[],none,⟨10,6,0⟩⟩
def t5_1445jobs0 : List Job := [⟨plan2911,[⟨8,0,3⟩],(some ⟨8,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan2911,[⟨8,1,2⟩],(some ⟨8,1,2⟩),⟨9,4,(-1)⟩⟩]

def t5_1445jobs1 : List Job := [⟨plan2911,[⟨8,1,3⟩],(some ⟨8,1,3⟩),⟨9,3,(-2)⟩⟩]

def t5_1445jobs : List Job := t5_1445jobs0++t5_1445jobs1




def t5_1446root : Job := ⟨plan4931,[],none,⟨10,6,0⟩⟩
def t5_1446jobs0 : List Job := [⟨plan4931,[],none,⟨10,6,0⟩⟩]

def t5_1446jobs : List Job := t5_1446jobs0




def t5_1447root : Job := ⟨plan4932,[],none,⟨10,6,0⟩⟩
def t5_1447jobs0 : List Job := [⟨plan4932,[],none,⟨10,6,0⟩⟩]

def t5_1447jobs : List Job := t5_1447jobs0




def t5_1448root : Job := ⟨plan3992,[],none,⟨10,1,0⟩⟩
def t5_1448jobs0 : List Job := [⟨plan3992,[],none,⟨10,1,0⟩⟩]

def t5_1448jobs : List Job := t5_1448jobs0




def t5_1449root : Job := ⟨plan4422,[],none,⟨10,3,0⟩⟩
def t5_1449jobs0 : List Job := [⟨plan4422,[],none,⟨10,3,0⟩⟩]

def t5_1449jobs : List Job := t5_1449jobs0




def t5_1450root : Job := ⟨plan4423,[],none,⟨10,3,0⟩⟩
def t5_1450jobs0 : List Job := [⟨plan4423,[],none,⟨10,3,0⟩⟩]

def t5_1450jobs : List Job := t5_1450jobs0




def t5_1451root : Job := ⟨plan4424,[],none,⟨10,3,0⟩⟩
def t5_1451jobs0 : List Job := [⟨plan4424,[],none,⟨10,3,0⟩⟩]

def t5_1451jobs : List Job := t5_1451jobs0




def t5_1452root : Job := ⟨plan4933,[],none,⟨10,6,0⟩⟩
def t5_1452jobs0 : List Job := [⟨plan4933,[],none,⟨10,6,0⟩⟩]

def t5_1452jobs : List Job := t5_1452jobs0




def t5_1453root : Job := ⟨plan4934,[],none,⟨10,6,0⟩⟩
def t5_1453jobs0 : List Job := [⟨plan4934,[],none,⟨10,6,0⟩⟩]

def t5_1453jobs : List Job := t5_1453jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


