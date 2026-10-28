-- Prove2me | Definitions.Def_D1Bound5_FirstPairGeometryData_Definitions_002
-- name    : D1Bound5_FirstPairGeometryData_Definitions_002
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:11:06.958179+00:00
-- url     : https://prove2.me/theorems/c18fa4d7-94b9-4d44-aa63-74a9f42b29d9
-- title:
--   First Pair Geometry Data 002
-- statement:
--   Coordinate-level link to the previously checked first-pair lists. The named objects in this bundle include `firstPairGeometryRows`, `firstPairGeometryRowsAt`.
-- source:
--   D1Bound5/FirstPairGeometryData.lean, lines 344-345, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a; D1Bound5/FirstPairGeometryData.lean, lines 393-395, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_FirstPairGeometryData_Definitions_001

section
namespace D1Bound5
open QuadInt



namespace FirstPairGeometryRow






























end FirstPairGeometryRow

set_option maxHeartbeats 0
set_option maxRecDepth 100000





































































































































































def firstPairGeometryRows : List FirstPairGeometryRow :=
  [firstPairGeometryRow_0,firstPairGeometryRow_1,firstPairGeometryRow_2,firstPairGeometryRow_3,firstPairGeometryRow_4,firstPairGeometryRow_5,firstPairGeometryRow_6,firstPairGeometryRow_7,firstPairGeometryRow_8,firstPairGeometryRow_9,firstPairGeometryRow_10,firstPairGeometryRow_11,firstPairGeometryRow_12,firstPairGeometryRow_13,firstPairGeometryRow_14,firstPairGeometryRow_15,firstPairGeometryRow_16,firstPairGeometryRow_17,firstPairGeometryRow_18,firstPairGeometryRow_19,firstPairGeometryRow_20,firstPairGeometryRow_21,firstPairGeometryRow_22,firstPairGeometryRow_23,firstPairGeometryRow_24,firstPairGeometryRow_25,firstPairGeometryRow_26,firstPairGeometryRow_27,firstPairGeometryRow_28,firstPairGeometryRow_29,firstPairGeometryRow_30,firstPairGeometryRow_31,firstPairGeometryRow_32,firstPairGeometryRow_33,firstPairGeometryRow_34,firstPairGeometryRow_35,firstPairGeometryRow_36,firstPairGeometryRow_37,firstPairGeometryRow_38,firstPairGeometryRow_39,firstPairGeometryRow_40]



/-- Coordinate-level link to the previously checked first-pair lists. -/
def firstPairGeometryRowsAt (tau nu : ℤ) : List ((ℤ × ℤ) × (ℤ × ℤ)) :=
  ((firstPairGeometryRows.filter (fun r => r.tau=tau ∧ r.nu=nu)).map (fun r => (r.a,r.b)))





















end D1Bound5
end


