-- Prove2me | Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_MarkerResidualPartition
-- name    : Sensitivity214439_PairedSemantic_Solutions_MarkerResidualPartition
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T19:45:44.362796+00:00
-- url     : https://prove2.me/theorems/33638a5f-82bd-485f-b4d9-032b2d7ba361
-- title:
--   Converted destinations and residual marker capacity
-- statement:
--   Partition a source's active outside destinations into converted destinations lying in the low-row set and external destinations lying outside it. The residual marker capacity is the total outside count, except that a guard head subtracts its external count:
--
--   $$\mathrm{capacity}=|\mathrm{outside}|-
--   \begin{cases}|\mathrm{external}|,&\text{for a guard head},\\0,&\text{otherwise}.\end{cases}$$
--
--   This keeps the exact uncompressed low-directed incidence allowance while charging non-low external checks separately.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/MarkerResidualPartition.lean lines 17–22; SHA256 881ea63e546acb25cea252119d46eec55aec1167cad50f3386b3881bd134ea07; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Fin
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

namespace SensitivityGuardEvents
end SensitivityGuardEvents
namespace SensitivityHighHeadGuardBridge
end SensitivityHighHeadGuardBridge
namespace SensitivityIndexedGuardResiduals
end SensitivityIndexedGuardResiduals
namespace SensitivityMarkedSocketPopulation
end SensitivityMarkedSocketPopulation
namespace SensitivityMarkerResidualPartition
end SensitivityMarkerResidualPartition
namespace SensitivityOperativeHeads
end SensitivityOperativeHeads
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction



/-! Marker capacities after removing external guard-event slots. The
uncompressed converted count is retained separately from any later pricing
compression for repeated guards in one source macro. -/
namespace SensitivityMarkerResidualPartition

noncomputable section
open scoped Classical BigOperators
open SensitivityRankedConstruction SensitivityGuardEvents SensitivityHighHeadGuardBridge
open SensitivityIndexedGuardResiduals SensitivityOperativeHeads SensitivityMarkedSocketPopulation
set_option autoImplicit false

variable {V S M B I Color : Type} {L : ℕ}

def converted (outside low : Finset V) : Finset V := outside.filter fun w => w ∈ low

def external (outside low : Finset V) : Finset V := outside.filter fun w => w ∉ low

def capacity (outside low : Finset V) (isGuard : Prop) [Decidable isGuard] : ℕ :=
  outside.card - if isGuard then (external outside low).card else 0





















end
end SensitivityMarkerResidualPartition


