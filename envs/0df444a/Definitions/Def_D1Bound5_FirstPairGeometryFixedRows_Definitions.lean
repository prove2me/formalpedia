-- Prove2me | Definitions.Def_D1Bound5_FirstPairGeometryFixedRows_Definitions
-- name    : D1Bound5_FirstPairGeometryFixedRows_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:11:17.486026+00:00
-- url     : https://prove2.me/theorems/6573b862-4528-46eb-968a-4e3114aef58f
-- title:
--   First Pair Geometry Fixed Rows
-- statement:
--   Exact equality of the pair and all five evaluated coefficient parameters. No field equivalence or polynomial bound is inferred by this data link. The named objects in this bundle include `FirstPairGeometryMatches`, `instDecidableFirstPairGeometryMatches`.
-- source:
--   D1Bound5/FirstPairGeometryFixedRows.lean, lines 6-10, SHA-256 84225093eb3f30b90e3cc61b11e72d39cd0cb1bab3442a3d330db9c6b02d9f97; D1Bound5/FirstPairGeometryFixedRows.lean, lines 12-15, SHA-256 84225093eb3f30b90e3cc61b11e72d39cd0cb1bab3442a3d330db9c6b02d9f97. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_FirstPairGeometryData_Definitions_001
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_001
import Definitions.Def_D1Bound5_OneSmallRows_Definitions

section
namespace D1Bound5

/-- Exact equality of the pair and all five evaluated coefficient parameters.
No field equivalence or polynomial bound is inferred by this data link. -/
def FirstPairGeometryMatches (g : FirstPairGeometryRow) (r : OneSmallCutoffRow) : Prop :=
  g.tau=r.triple.tau ∧ g.nu=r.triple.nu ∧ g.a=r.triple.a ∧ g.b=r.triple.b ∧
  g.M2=r.M2 ∧ g.Mn=r.Mn ∧ g.M3=r.M3 ∧ g.M4=r.M4 ∧ g.M5=r.M5

instance (g : FirstPairGeometryRow) (r : OneSmallCutoffRow) :
    Decidable (FirstPairGeometryMatches g r) := by
  unfold FirstPairGeometryMatches
  infer_instance

set_option maxRecDepth 100000
set_option maxHeartbeats 0





















































































end D1Bound5
end


