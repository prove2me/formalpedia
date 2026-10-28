-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks040
-- name    : Sensitivity213981Formal_Endpoint22ReachChecks040
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:27:16.98515+00:00
-- url     : https://prove2.me/theorems/0bd50b0e-b698-48b5-9b3d-4715f3e17eb6
-- title:
--   Endpoint22 Reach Checks040 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Checks040 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.t5_1374root`, `ThreeBoundEndpoint22Reachable.t5_1374jobs0`, `ThreeBoundEndpoint22Reachable.t5_1374jobs`, `ThreeBoundEndpoint22Reachable.t5_1375root`, `ThreeBoundEndpoint22Reachable.t5_1375jobs0`, `ThreeBoundEndpoint22Reachable.t5_1375jobs`, `ThreeBoundEndpoint22Reachable.t5_1376root`, `ThreeBoundEndpoint22Reachable.t5_1376jobs0`, `ThreeBoundEndpoint22Reachable.t5_1376jobs`, `ThreeBoundEndpoint22Reachable.t5_1377root`, `ThreeBoundEndpoint22Reachable.t5_1377jobs0`, `ThreeBoundEndpoint22Reachable.t5_1377jobs`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachChecks040.lean, lines 1–430.

import Definitions.Def_Sensitivity213981Formal_Endpoint22PackedRecordTree
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans039
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans041
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans045
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans050
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

def t5_1361root : Job := ⟨plan3981,[],none,⟨10,1,0⟩⟩
def t5_1361jobs0 : List Job := [⟨plan3981,[],none,⟨10,1,0⟩⟩]

def t5_1361jobs : List Job := t5_1361jobs0




def t5_1362root : Job := ⟨plan3982,[],none,⟨10,1,0⟩⟩
def t5_1362jobs0 : List Job := [⟨plan3982,[],none,⟨10,1,0⟩⟩]

def t5_1362jobs : List Job := t5_1362jobs0




def t5_1363root : Job := ⟨plan4389,[],none,⟨10,3,0⟩⟩
def t5_1363jobs0 : List Job := [⟨plan4389,[],none,⟨10,3,0⟩⟩]

def t5_1363jobs : List Job := t5_1363jobs0




def t5_1364root : Job := ⟨plan4390,[],none,⟨10,3,0⟩⟩
def t5_1364jobs0 : List Job := [⟨plan4390,[],none,⟨10,3,0⟩⟩]

def t5_1364jobs : List Job := t5_1364jobs0




def t5_1365root : Job := ⟨plan4391,[],none,⟨10,3,0⟩⟩
def t5_1365jobs0 : List Job := [⟨plan4391,[],none,⟨10,3,0⟩⟩]

def t5_1365jobs : List Job := t5_1365jobs0




def t5_1366root : Job := ⟨plan4392,[],none,⟨10,3,0⟩⟩
def t5_1366jobs0 : List Job := [⟨plan4392,[],none,⟨10,3,0⟩⟩]

def t5_1366jobs : List Job := t5_1366jobs0




def t5_1367root : Job := ⟨plan4393,[],none,⟨10,3,0⟩⟩
def t5_1367jobs0 : List Job := [⟨plan4393,[],none,⟨10,3,0⟩⟩]

def t5_1367jobs : List Job := t5_1367jobs0




def t5_1368root : Job := ⟨plan4394,[],none,⟨10,3,0⟩⟩
def t5_1368jobs0 : List Job := [⟨plan4394,[],none,⟨10,3,0⟩⟩]

def t5_1368jobs : List Job := t5_1368jobs0




def t5_1369root : Job := ⟨plan4395,[],none,⟨10,3,0⟩⟩
def t5_1369jobs0 : List Job := [⟨plan4395,[],none,⟨10,3,0⟩⟩]

def t5_1369jobs : List Job := t5_1369jobs0




def t5_1370root : Job := ⟨plan3983,[],none,⟨10,1,0⟩⟩
def t5_1370jobs0 : List Job := [⟨plan3983,[],none,⟨10,1,0⟩⟩]

def t5_1370jobs : List Job := t5_1370jobs0




def t5_1371root : Job := ⟨plan4396,[],none,⟨10,3,0⟩⟩
def t5_1371jobs0 : List Job := [⟨plan4396,[],none,⟨10,3,0⟩⟩]

def t5_1371jobs : List Job := t5_1371jobs0




def t5_1372root : Job := ⟨plan4397,[],none,⟨10,3,0⟩⟩
def t5_1372jobs0 : List Job := [⟨plan4397,[],none,⟨10,3,0⟩⟩]

def t5_1372jobs : List Job := t5_1372jobs0




def t5_1373root : Job := ⟨plan4398,[],none,⟨10,3,0⟩⟩
def t5_1373jobs0 : List Job := [⟨plan4398,[],none,⟨10,3,0⟩⟩]

def t5_1373jobs : List Job := t5_1373jobs0




def t5_1374root : Job := ⟨plan4399,[],none,⟨10,3,0⟩⟩
def t5_1374jobs0 : List Job := [⟨plan4399,[],none,⟨10,3,0⟩⟩]

def t5_1374jobs : List Job := t5_1374jobs0




def t5_1375root : Job := ⟨plan4400,[],none,⟨10,3,0⟩⟩
def t5_1375jobs0 : List Job := [⟨plan4400,[],none,⟨10,3,0⟩⟩]

def t5_1375jobs : List Job := t5_1375jobs0




def t5_1376root : Job := ⟨plan3756,[],none,⟨10,0,0⟩⟩
def t5_1376jobs0 : List Job := [⟨plan3756,[],none,⟨10,0,0⟩⟩]

def t5_1376jobs : List Job := t5_1376jobs0




def t5_1377root : Job := ⟨plan3984,[],none,⟨10,1,0⟩⟩
def t5_1377jobs0 : List Job := [⟨plan3984,[],none,⟨10,1,0⟩⟩]

def t5_1377jobs : List Job := t5_1377jobs0




def t5_1378root : Job := ⟨plan3985,[],none,⟨10,1,0⟩⟩
def t5_1378jobs0 : List Job := [⟨plan2608,[⟨8,0,1⟩],(some ⟨8,0,1⟩),⟨10,0,(-1)⟩⟩,⟨plan2608,[⟨8,1,0⟩],(some ⟨8,1,0⟩),⟨9,1,1⟩⟩]

def t5_1378jobs1 : List Job := [⟨plan2608,[⟨8,1,1⟩],(some ⟨8,1,1⟩),⟨9,0,0⟩⟩]

def t5_1378jobs : List Job := t5_1378jobs0++t5_1378jobs1




def t5_1379root : Job := ⟨plan3986,[],none,⟨10,1,0⟩⟩
def t5_1379jobs0 : List Job := [⟨plan3986,[],none,⟨10,1,0⟩⟩]

def t5_1379jobs : List Job := t5_1379jobs0




def t5_1380root : Job := ⟨plan4401,[],none,⟨10,3,0⟩⟩
def t5_1380jobs0 : List Job := [⟨plan4401,[],none,⟨10,3,0⟩⟩]

def t5_1380jobs : List Job := t5_1380jobs0




def t5_1381root : Job := ⟨plan4402,[],none,⟨10,3,0⟩⟩
def t5_1381jobs0 : List Job := [⟨plan2713,[⟨8,0,2⟩],(some ⟨8,0,2⟩),⟨10,1,(-2)⟩⟩,⟨plan2713,[⟨8,1,1⟩],(some ⟨8,1,1⟩),⟨9,2,0⟩⟩]

def t5_1381jobs1 : List Job := [⟨plan2713,[⟨8,1,2⟩],(some ⟨8,1,2⟩),⟨9,1,(-1)⟩⟩]

def t5_1381jobs : List Job := t5_1381jobs0++t5_1381jobs1




def t5_1382root : Job := ⟨plan4403,[],none,⟨10,3,0⟩⟩
def t5_1382jobs0 : List Job := [⟨plan2714,[⟨8,0,2⟩],(some ⟨8,0,2⟩),⟨10,1,(-2)⟩⟩,⟨plan2714,[⟨8,1,1⟩],(some ⟨8,1,1⟩),⟨9,2,0⟩⟩]

def t5_1382jobs1 : List Job := [⟨plan2714,[⟨8,1,2⟩],(some ⟨8,1,2⟩),⟨9,1,(-1)⟩⟩]

def t5_1382jobs : List Job := t5_1382jobs0++t5_1382jobs1




def t5_1383root : Job := ⟨plan4404,[],none,⟨10,3,0⟩⟩
def t5_1383jobs0 : List Job := [⟨plan4404,[],none,⟨10,3,0⟩⟩]

def t5_1383jobs : List Job := t5_1383jobs0




def t5_1384root : Job := ⟨plan4405,[],none,⟨10,3,0⟩⟩
def t5_1384jobs0 : List Job := [⟨plan2716,[⟨8,0,2⟩],(some ⟨8,0,2⟩),⟨10,1,(-2)⟩⟩,⟨plan2716,[⟨8,1,1⟩],(some ⟨8,1,1⟩),⟨9,2,0⟩⟩]

def t5_1384jobs1 : List Job := [⟨plan2716,[⟨8,1,2⟩],(some ⟨8,1,2⟩),⟨9,1,(-1)⟩⟩]

def t5_1384jobs : List Job := t5_1384jobs0++t5_1384jobs1




def t5_1385root : Job := ⟨plan4406,[],none,⟨10,3,0⟩⟩
def t5_1385jobs0 : List Job := [⟨plan4406,[],none,⟨10,3,0⟩⟩]

def t5_1385jobs : List Job := t5_1385jobs0




def t5_1386root : Job := ⟨plan3987,[],none,⟨10,1,0⟩⟩
def t5_1386jobs0 : List Job := [⟨plan3987,[],none,⟨10,1,0⟩⟩]

def t5_1386jobs : List Job := t5_1386jobs0




def t5_1387root : Job := ⟨plan4407,[],none,⟨10,3,0⟩⟩
def t5_1387jobs0 : List Job := [⟨plan4407,[],none,⟨10,3,0⟩⟩]

def t5_1387jobs : List Job := t5_1387jobs0




def t5_1388root : Job := ⟨plan4408,[],none,⟨10,3,0⟩⟩
def t5_1388jobs0 : List Job := [⟨plan4408,[],none,⟨10,3,0⟩⟩]

def t5_1388jobs : List Job := t5_1388jobs0




def t5_1389root : Job := ⟨plan4409,[],none,⟨10,3,0⟩⟩
def t5_1389jobs0 : List Job := [⟨plan4409,[],none,⟨10,3,0⟩⟩]

def t5_1389jobs : List Job := t5_1389jobs0




def t5_1390root : Job := ⟨plan4410,[],none,⟨10,3,0⟩⟩
def t5_1390jobs0 : List Job := [⟨plan4410,[],none,⟨10,3,0⟩⟩]

def t5_1390jobs : List Job := t5_1390jobs0




def t5_1391root : Job := ⟨plan4892,[],none,⟨10,6,0⟩⟩
def t5_1391jobs0 : List Job := [⟨plan4892,[],none,⟨10,6,0⟩⟩]

def t5_1391jobs : List Job := t5_1391jobs0




def t5_1392root : Job := ⟨plan4893,[],none,⟨10,6,0⟩⟩
def t5_1392jobs0 : List Job := [⟨plan4893,[],none,⟨10,6,0⟩⟩]

def t5_1392jobs : List Job := t5_1392jobs0




def t5_1393root : Job := ⟨plan4894,[],none,⟨10,6,0⟩⟩
def t5_1393jobs0 : List Job := [⟨plan4894,[],none,⟨10,6,0⟩⟩]

def t5_1393jobs : List Job := t5_1393jobs0




def t5_1394root : Job := ⟨plan4895,[],none,⟨10,6,0⟩⟩
def t5_1394jobs0 : List Job := [⟨plan4895,[],none,⟨10,6,0⟩⟩]

def t5_1394jobs : List Job := t5_1394jobs0




def t5_1395root : Job := ⟨plan4896,[],none,⟨10,6,0⟩⟩
def t5_1395jobs0 : List Job := [⟨plan4896,[],none,⟨10,6,0⟩⟩]

def t5_1395jobs : List Job := t5_1395jobs0




def t5_1396root : Job := ⟨plan4897,[],none,⟨10,6,0⟩⟩
def t5_1396jobs0 : List Job := [⟨plan4897,[],none,⟨10,6,0⟩⟩]

def t5_1396jobs : List Job := t5_1396jobs0




def t5_1397root : Job := ⟨plan4898,[],none,⟨10,6,0⟩⟩
def t5_1397jobs0 : List Job := [⟨plan4898,[],none,⟨10,6,0⟩⟩]

def t5_1397jobs : List Job := t5_1397jobs0



end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


