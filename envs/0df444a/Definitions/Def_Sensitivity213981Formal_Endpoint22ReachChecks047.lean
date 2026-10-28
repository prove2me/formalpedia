-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks047
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks047
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:25:26.625004+00:00
-- url     : https://prove2.me/theorems/59f7ff75-8c1d-4743-ac9c-5a9d0f33ad3f
-- title:
--   Endpoint22 Reach Checks047 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks047 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t5_1653root`, `ThreeBoundEndpoint22Reachable.t5_1653jobs0`, `ThreeBoundEndpoint22Reachable.t5_1653jobs`, `ThreeBoundEndpoint22Reachable.t5_1642jobs1`, `ThreeBoundEndpoint22Reachable.t5_1654root`, `ThreeBoundEndpoint22Reachable.t5_1654jobs0`, `ThreeBoundEndpoint22Reachable.t5_1654jobs`, `ThreeBoundEndpoint22Reachable.t5_1655root`, `ThreeBoundEndpoint22Reachable.t5_1655jobs0`, `ThreeBoundEndpoint22Reachable.t5_1655jobs`, `ThreeBoundEndpoint22Reachable.t5_1656root`, `ThreeBoundEndpoint22Reachable.t5_1656jobs0`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks047.lean, lines 1–859.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans046
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans051
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans052
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans055
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans065
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans067
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans069
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

def t5_1642root : Job := ⟨plan4447,[],none,⟨10,3,0⟩⟩
def t5_1642jobs0 : List Job := [⟨plan2860,[⟨9,0,2⟩],(some ⟨9,0,2⟩),⟨10,1,(-2)⟩⟩,⟨plan2860,[⟨9,1,1⟩],(some ⟨9,1,1⟩),⟨9,2,0⟩⟩,⟨plan2860,[⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨9,1,(-1)⟩⟩,⟨plan2860,[⟨9,2,0⟩],(some ⟨9,2,0⟩),⟨8,3,2⟩⟩]

def t5_1642jobs1 : List Job := [⟨plan2860,[⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨8,2,1⟩⟩,⟨plan2860,[⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨8,1,0⟩⟩]

def t5_1642jobs : List Job := t5_1642jobs0++t5_1642jobs1




def t5_1643root : Job := ⟨plan4448,[],none,⟨10,3,0⟩⟩
def t5_1643jobs0 : List Job := [⟨plan4448,[],none,⟨10,3,0⟩⟩]

def t5_1643jobs : List Job := t5_1643jobs0




def t5_1644root : Job := ⟨plan4989,[],none,⟨10,6,0⟩⟩
def t5_1644jobs0 : List Job := [⟨plan4989,[],none,⟨10,6,0⟩⟩]

def t5_1644jobs : List Job := t5_1644jobs0




def t5_1645root : Job := ⟨plan4990,[],none,⟨10,6,0⟩⟩
def t5_1645jobs0 : List Job := [⟨plan3078,[⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan3078,[⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨9,4,(-1)⟩⟩,⟨plan3078,[⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨9,3,(-2)⟩⟩]

def t5_1645jobs1 : List Job := [⟨plan3078,[⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨8,5,1⟩⟩,⟨plan3078,[⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨8,4,0⟩⟩]

def t5_1645jobs : List Job := t5_1645jobs0++t5_1645jobs1




def t5_1646root : Job := ⟨plan4991,[],none,⟨10,6,0⟩⟩
def t5_1646jobs0 : List Job := [⟨plan4991,[],none,⟨10,6,0⟩⟩]

def t5_1646jobs : List Job := t5_1646jobs0




def t5_1647root : Job := ⟨plan4992,[],none,⟨10,6,0⟩⟩
def t5_1647jobs0 : List Job := [⟨plan4992,[],none,⟨10,6,0⟩⟩]

def t5_1647jobs : List Job := t5_1647jobs0




def t5_1648root : Job := ⟨plan4993,[],none,⟨10,6,0⟩⟩
def t5_1648jobs0 : List Job := [⟨plan3081,[⟨9,0,3⟩],(some ⟨9,0,3⟩),⟨10,3,(-3)⟩⟩,⟨plan3081,[⟨9,1,2⟩],(some ⟨9,1,2⟩),⟨9,4,(-1)⟩⟩,⟨plan3081,[⟨9,1,3⟩],(some ⟨9,1,3⟩),⟨9,3,(-2)⟩⟩]

def t5_1648jobs1 : List Job := [⟨plan3081,[⟨9,2,1⟩],(some ⟨9,2,1⟩),⟨8,5,1⟩⟩,⟨plan3081,[⟨9,2,2⟩],(some ⟨9,2,2⟩),⟨8,4,0⟩⟩]

def t5_1648jobs : List Job := t5_1648jobs0++t5_1648jobs1




def t5_1649root : Job := ⟨plan4994,[],none,⟨10,6,0⟩⟩
def t5_1649jobs0 : List Job := [⟨plan4994,[],none,⟨10,6,0⟩⟩]

def t5_1649jobs : List Job := t5_1649jobs0




def t5_1650root : Job := ⟨plan5313,[],none,⟨10,10,0⟩⟩
def t5_1650jobs0 : List Job := [⟨plan5313,[],none,⟨10,10,0⟩⟩]

def t5_1650jobs : List Job := t5_1650jobs0




def t5_1651root : Job := ⟨plan5314,[],none,⟨10,10,0⟩⟩
def t5_1651jobs0 : List Job := [⟨plan5314,[],none,⟨10,10,0⟩⟩]

def t5_1651jobs : List Job := t5_1651jobs0




def t5_1652root : Job := ⟨plan5315,[],none,⟨10,10,0⟩⟩
def t5_1652jobs0 : List Job := [⟨plan5315,[],none,⟨10,10,0⟩⟩]

def t5_1652jobs : List Job := t5_1652jobs0




def t5_1653root : Job := ⟨plan5316,[],none,⟨10,10,0⟩⟩
def t5_1653jobs0 : List Job := [⟨plan5316,[],none,⟨10,10,0⟩⟩]

def t5_1653jobs : List Job := t5_1653jobs0




def t5_1654root : Job := ⟨plan5317,[],none,⟨10,10,0⟩⟩
def t5_1654jobs0 : List Job := [⟨plan5317,[],none,⟨10,10,0⟩⟩]

def t5_1654jobs : List Job := t5_1654jobs0




def t5_1655root : Job := ⟨plan5318,[],none,⟨10,10,0⟩⟩
def t5_1655jobs0 : List Job := [⟨plan5318,[],none,⟨10,10,0⟩⟩]

def t5_1655jobs : List Job := t5_1655jobs0




def t5_1656root : Job := ⟨plan5319,[],none,⟨10,10,0⟩⟩
def t5_1656jobs0 : List Job := [⟨plan5319,[],none,⟨10,10,0⟩⟩]

def t5_1656jobs : List Job := t5_1656jobs0




def t5_1657root : Job := ⟨plan4449,[],none,⟨10,3,0⟩⟩
def t5_1657jobs0 : List Job := [⟨plan4449,[],none,⟨10,3,0⟩⟩]

def t5_1657jobs : List Job := t5_1657jobs0




def t5_1658root : Job := ⟨plan4995,[],none,⟨10,6,0⟩⟩
def t5_1658jobs0 : List Job := [⟨plan4995,[],none,⟨10,6,0⟩⟩]

def t5_1658jobs : List Job := t5_1658jobs0




def t5_1659root : Job := ⟨plan4996,[],none,⟨10,6,0⟩⟩
def t5_1659jobs0 : List Job := [⟨plan4996,[],none,⟨10,6,0⟩⟩]

def t5_1659jobs : List Job := t5_1659jobs0




def t5_1660root : Job := ⟨plan4997,[],none,⟨10,6,0⟩⟩
def t5_1660jobs0 : List Job := [⟨plan4997,[],none,⟨10,6,0⟩⟩]

def t5_1660jobs : List Job := t5_1660jobs0




def t5_1661root : Job := ⟨plan5320,[],none,⟨10,10,0⟩⟩
def t5_1661jobs0 : List Job := [⟨plan5320,[],none,⟨10,10,0⟩⟩]

def t5_1661jobs : List Job := t5_1661jobs0




def t5_1662root : Job := ⟨plan5321,[],none,⟨10,10,0⟩⟩
def t5_1662jobs0 : List Job := [⟨plan5321,[],none,⟨10,10,0⟩⟩]

def t5_1662jobs : List Job := t5_1662jobs0




def t5_1663root : Job := ⟨plan5322,[],none,⟨10,10,0⟩⟩
def t5_1663jobs0 : List Job := [⟨plan5322,[],none,⟨10,10,0⟩⟩]

def t5_1663jobs : List Job := t5_1663jobs0




def t5_1664root : Job := ⟨plan5323,[],none,⟨10,10,0⟩⟩
def t5_1664jobs0 : List Job := [⟨plan5323,[],none,⟨10,10,0⟩⟩]

def t5_1664jobs : List Job := t5_1664jobs0




def t5_1665root : Job := ⟨plan4998,[],none,⟨10,6,0⟩⟩
def t5_1665jobs0 : List Job := [⟨plan4998,[],none,⟨10,6,0⟩⟩]

def t5_1665jobs : List Job := t5_1665jobs0




def t5_1666root : Job := ⟨plan5324,[],none,⟨10,10,0⟩⟩
def t5_1666jobs0 : List Job := [⟨plan5324,[],none,⟨10,10,0⟩⟩]

def t5_1666jobs : List Job := t5_1666jobs0




def t5_1667root : Job := ⟨plan5325,[],none,⟨10,10,0⟩⟩
def t5_1667jobs0 : List Job := [⟨plan5325,[],none,⟨10,10,0⟩⟩]

def t5_1667jobs : List Job := t5_1667jobs0




def t5_1668root : Job := ⟨plan5326,[],none,⟨10,10,0⟩⟩
def t5_1668jobs0 : List Job := [⟨plan5326,[],none,⟨10,10,0⟩⟩]

def t5_1668jobs : List Job := t5_1668jobs0




def t5_1669root : Job := ⟨plan5327,[],none,⟨10,10,0⟩⟩
def t5_1669jobs0 : List Job := [⟨plan5327,[],none,⟨10,10,0⟩⟩]

def t5_1669jobs : List Job := t5_1669jobs0




def t5_1670root : Job := ⟨plan5328,[],none,⟨10,10,0⟩⟩
def t5_1670jobs0 : List Job := [⟨plan5328,[],none,⟨10,10,0⟩⟩]

def t5_1670jobs : List Job := t5_1670jobs0




def t5_1671root : Job := ⟨plan5329,[],none,⟨10,10,0⟩⟩
def t5_1671jobs0 : List Job := [⟨plan5329,[],none,⟨10,10,0⟩⟩]

def t5_1671jobs : List Job := t5_1671jobs0




def t5_1672root : Job := ⟨plan5330,[],none,⟨10,10,0⟩⟩
def t5_1672jobs0 : List Job := [⟨plan5330,[],none,⟨10,10,0⟩⟩]

def t5_1672jobs : List Job := t5_1672jobs0




def t5_1673root : Job := ⟨plan5331,[],none,⟨10,10,0⟩⟩
def t5_1673jobs0 : List Job := [⟨plan5331,[],none,⟨10,10,0⟩⟩]

def t5_1673jobs : List Job := t5_1673jobs0




def t5_1674root : Job := ⟨plan5332,[],none,⟨10,10,0⟩⟩
def t5_1674jobs0 : List Job := [⟨plan5332,[],none,⟨10,10,0⟩⟩]

def t5_1674jobs : List Job := t5_1674jobs0




def t5_1675root : Job := ⟨plan5333,[],none,⟨10,10,0⟩⟩
def t5_1675jobs0 : List Job := [⟨plan5333,[],none,⟨10,10,0⟩⟩]

def t5_1675jobs : List Job := t5_1675jobs0




def t5_1676root : Job := ⟨plan5334,[],none,⟨10,10,0⟩⟩
def t5_1676jobs0 : List Job := [⟨plan5334,[],none,⟨10,10,0⟩⟩]

def t5_1676jobs : List Job := t5_1676jobs0




def t5_1677root : Job := ⟨plan5335,[],none,⟨10,10,0⟩⟩
def t5_1677jobs0 : List Job := [⟨plan5335,[],none,⟨10,10,0⟩⟩]

def t5_1677jobs : List Job := t5_1677jobs0




def t5_1678root : Job := ⟨plan5336,[],none,⟨10,10,0⟩⟩
def t5_1678jobs0 : List Job := [⟨plan5336,[],none,⟨10,10,0⟩⟩]

def t5_1678jobs : List Job := t5_1678jobs0




def t5_1679root : Job := ⟨plan5337,[],none,⟨10,10,0⟩⟩
def t5_1679jobs0 : List Job := [⟨plan5337,[],none,⟨10,10,0⟩⟩]

def t5_1679jobs : List Job := t5_1679jobs0




def t5_1680root : Job := ⟨plan5338,[],none,⟨10,10,0⟩⟩
def t5_1680jobs0 : List Job := [⟨plan5338,[],none,⟨10,10,0⟩⟩]

def t5_1680jobs : List Job := t5_1680jobs0




def t5_1681root : Job := ⟨plan5339,[],none,⟨10,10,0⟩⟩
def t5_1681jobs0 : List Job := [⟨plan5339,[],none,⟨10,10,0⟩⟩]

def t5_1681jobs : List Job := t5_1681jobs0




def t5_1682root : Job := ⟨plan5340,[],none,⟨10,10,0⟩⟩
def t5_1682jobs0 : List Job := [⟨plan5340,[],none,⟨10,10,0⟩⟩]

def t5_1682jobs : List Job := t5_1682jobs0




def t5_1683root : Job := ⟨plan5341,[],none,⟨10,10,0⟩⟩
def t5_1683jobs0 : List Job := [⟨plan5341,[],none,⟨10,10,0⟩⟩]

def t5_1683jobs : List Job := t5_1683jobs0




def t6_0root : Job := ⟨plan6434,[],none,⟨15,3,0⟩⟩
def t6_0jobs0 : List Job := [⟨plan6434,[],none,⟨15,3,0⟩⟩]

def t6_0jobs : List Job := t6_0jobs0




def t6_1root : Job := ⟨plan6320,[],none,⟨15,1,0⟩⟩
def t6_1jobs0 : List Job := [⟨plan6320,[],none,⟨15,1,0⟩⟩]

def t6_1jobs : List Job := t6_1jobs0




def t6_2root : Job := ⟨plan6435,[],none,⟨15,3,0⟩⟩
def t6_2jobs0 : List Job := [⟨plan6435,[],none,⟨15,3,0⟩⟩]

def t6_2jobs : List Job := t6_2jobs0




def t6_3root : Job := ⟨plan6436,[],none,⟨15,3,0⟩⟩
def t6_3jobs0 : List Job := [⟨plan6436,[],none,⟨15,3,0⟩⟩]

def t6_3jobs : List Job := t6_3jobs0




def t6_4root : Job := ⟨plan6437,[],none,⟨15,3,0⟩⟩
def t6_4jobs0 : List Job := [⟨plan6437,[],none,⟨15,3,0⟩⟩]

def t6_4jobs : List Job := t6_4jobs0




def t6_5root : Job := ⟨plan6694,[],none,⟨15,6,0⟩⟩
def t6_5jobs0 : List Job := [⟨plan6694,[],none,⟨15,6,0⟩⟩]

def t6_5jobs : List Job := t6_5jobs0




def t6_6root : Job := ⟨plan6695,[],none,⟨15,6,0⟩⟩
def t6_6jobs0 : List Job := [⟨plan6695,[],none,⟨15,6,0⟩⟩]

def t6_6jobs : List Job := t6_6jobs0




def t6_7root : Job := ⟨plan6696,[],none,⟨15,6,0⟩⟩
def t6_7jobs0 : List Job := [⟨plan6696,[],none,⟨15,6,0⟩⟩]

def t6_7jobs : List Job := t6_7jobs0




def t6_8root : Job := ⟨plan6697,[],none,⟨15,6,0⟩⟩
def t6_8jobs0 : List Job := [⟨plan6697,[],none,⟨15,6,0⟩⟩]

def t6_8jobs : List Job := t6_8jobs0




def t6_9root : Job := ⟨plan6698,[],none,⟨15,6,0⟩⟩
def t6_9jobs0 : List Job := [⟨plan6698,[],none,⟨15,6,0⟩⟩]

def t6_9jobs : List Job := t6_9jobs0




def t6_10root : Job := ⟨plan6699,[],none,⟨15,6,0⟩⟩
def t6_10jobs0 : List Job := [⟨plan6699,[],none,⟨15,6,0⟩⟩]

def t6_10jobs : List Job := t6_10jobs0




def t6_11root : Job := ⟨plan6700,[],none,⟨15,6,0⟩⟩
def t6_11jobs0 : List Job := [⟨plan6700,[],none,⟨15,6,0⟩⟩]

def t6_11jobs : List Job := t6_11jobs0




def t6_12root : Job := ⟨plan6701,[],none,⟨15,6,0⟩⟩
def t6_12jobs0 : List Job := [⟨plan6701,[],none,⟨15,6,0⟩⟩]

def t6_12jobs : List Job := t6_12jobs0




def t6_13root : Job := ⟨plan6321,[],none,⟨15,1,0⟩⟩
def t6_13jobs0 : List Job := [⟨plan6321,[],none,⟨15,1,0⟩⟩]

def t6_13jobs : List Job := t6_13jobs0




def t6_14root : Job := ⟨plan6438,[],none,⟨15,3,0⟩⟩
def t6_14jobs0 : List Job := [⟨plan6438,[],none,⟨15,3,0⟩⟩]

def t6_14jobs : List Job := t6_14jobs0




def t6_15root : Job := ⟨plan6439,[],none,⟨15,3,0⟩⟩
def t6_15jobs0 : List Job := [⟨plan6439,[],none,⟨15,3,0⟩⟩]

def t6_15jobs : List Job := t6_15jobs0




def t6_16root : Job := ⟨plan6440,[],none,⟨15,3,0⟩⟩
def t6_16jobs0 : List Job := [⟨plan6440,[],none,⟨15,3,0⟩⟩]

def t6_16jobs : List Job := t6_16jobs0




def t6_17root : Job := ⟨plan6283,[],none,⟨15,0,0⟩⟩
def t6_17jobs0 : List Job := [⟨plan6283,[],none,⟨15,0,0⟩⟩]

def t6_17jobs : List Job := t6_17jobs0




def t6_18root : Job := ⟨plan6322,[],none,⟨15,1,0⟩⟩
def t6_18jobs0 : List Job := [⟨plan6322,[],none,⟨15,1,0⟩⟩]

def t6_18jobs : List Job := t6_18jobs0




def t6_19root : Job := ⟨plan6323,[],none,⟨15,1,0⟩⟩
def t6_19jobs0 : List Job := [⟨plan6323,[],none,⟨15,1,0⟩⟩]

def t6_19jobs : List Job := t6_19jobs0




def t6_20root : Job := ⟨plan6324,[],none,⟨15,1,0⟩⟩
def t6_20jobs0 : List Job := [⟨plan6324,[],none,⟨15,1,0⟩⟩]

def t6_20jobs : List Job := t6_20jobs0




def t6_21root : Job := ⟨plan6441,[],none,⟨15,3,0⟩⟩
def t6_21jobs0 : List Job := [⟨plan6441,[],none,⟨15,3,0⟩⟩]

def t6_21jobs : List Job := t6_21jobs0




def t6_22root : Job := ⟨plan6442,[],none,⟨15,3,0⟩⟩
def t6_22jobs0 : List Job := [⟨plan6442,[],none,⟨15,3,0⟩⟩]

def t6_22jobs : List Job := t6_22jobs0




def t6_23root : Job := ⟨plan6443,[],none,⟨15,3,0⟩⟩
def t6_23jobs0 : List Job := [⟨plan6443,[],none,⟨15,3,0⟩⟩]

def t6_23jobs : List Job := t6_23jobs0




def t6_24root : Job := ⟨plan6444,[],none,⟨15,3,0⟩⟩
def t6_24jobs0 : List Job := [⟨plan6444,[],none,⟨15,3,0⟩⟩]

def t6_24jobs : List Job := t6_24jobs0




def t6_25root : Job := ⟨plan6445,[],none,⟨15,3,0⟩⟩
def t6_25jobs0 : List Job := [⟨plan6445,[],none,⟨15,3,0⟩⟩]

def t6_25jobs : List Job := t6_25jobs0




def t6_26root : Job := ⟨plan6446,[],none,⟨15,3,0⟩⟩
def t6_26jobs0 : List Job := [⟨plan6446,[],none,⟨15,3,0⟩⟩]

def t6_26jobs : List Job := t6_26jobs0




def t6_27root : Job := ⟨plan6447,[],none,⟨15,3,0⟩⟩
def t6_27jobs0 : List Job := [⟨plan6447,[],none,⟨15,3,0⟩⟩]

def t6_27jobs : List Job := t6_27jobs0




def t6_28root : Job := ⟨plan6702,[],none,⟨15,6,0⟩⟩
def t6_28jobs0 : List Job := [⟨plan6702,[],none,⟨15,6,0⟩⟩]

def t6_28jobs : List Job := t6_28jobs0




def t6_29root : Job := ⟨plan6703,[],none,⟨15,6,0⟩⟩
def t6_29jobs0 : List Job := [⟨plan6703,[],none,⟨15,6,0⟩⟩]

def t6_29jobs : List Job := t6_29jobs0




def t6_30root : Job := ⟨plan6704,[],none,⟨15,6,0⟩⟩
def t6_30jobs0 : List Job := [⟨plan6704,[],none,⟨15,6,0⟩⟩]

def t6_30jobs : List Job := t6_30jobs0




def t6_31root : Job := ⟨plan6705,[],none,⟨15,6,0⟩⟩
def t6_31jobs0 : List Job := [⟨plan6705,[],none,⟨15,6,0⟩⟩]

def t6_31jobs : List Job := t6_31jobs0




def t6_32root : Job := ⟨plan6706,[],none,⟨15,6,0⟩⟩
def t6_32jobs0 : List Job := [⟨plan6706,[],none,⟨15,6,0⟩⟩]

def t6_32jobs : List Job := t6_32jobs0




def t6_33root : Job := ⟨plan6707,[],none,⟨15,6,0⟩⟩
def t6_33jobs0 : List Job := [⟨plan6707,[],none,⟨15,6,0⟩⟩]

def t6_33jobs : List Job := t6_33jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


