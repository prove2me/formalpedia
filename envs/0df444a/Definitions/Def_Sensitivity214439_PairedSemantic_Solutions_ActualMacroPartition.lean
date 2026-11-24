-- Prove2me | Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_ActualMacroPartition
-- name    : Sensitivity214439_PairedSemantic_Solutions_ActualMacroPartition
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T20:33:32.378586+00:00
-- url     : https://prove2.me/theorems/0c2e53cd-f740-445c-9cf9-43d604c0a385
-- title:
--   Indexing actual macro classes and converted counts
-- statement:
--   Defines the tournament relation pulled back along a head numbering, the representative partition induced by equal macro coordinates, and each numbered head's residual guard budget after its outgoing numbered high neighbors. actualCounts assigns each represented guard macro the number of common active low destinations, giving the bounded-count data used in the finite macro model.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/ActualMacroPartition.lean lines 22–103; SHA256 00c3c9a00aefd3f14b8556963bbb6609146a357581f7f45c1f0fff4fb4c2b7c5; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_FiniteHeadReindexing
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_MacroConvertedIncidences
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_MacroPartitionCounts
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_MacroPartitionModel
import Definitions.Def_Sensitivity214439_Phase0_Solutions_RankedBooleanConstruction
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
import Mathlib.Data.Finset.Sigma
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

namespace SensitivityActualMacroPartition
end SensitivityActualMacroPartition
namespace SensitivityFiniteHeadReindexing
end SensitivityFiniteHeadReindexing
namespace SensitivityGuardEvents
end SensitivityGuardEvents
namespace SensitivityHighHeadGuardBridge
end SensitivityHighHeadGuardBridge
namespace SensitivityIndexedGuardResiduals
end SensitivityIndexedGuardResiduals
namespace SensitivityMacroConvertedIncidences
end SensitivityMacroConvertedIncidences
namespace SensitivityMacroPartitionModel
end SensitivityMacroPartitionModel
namespace SensitivityMarkerResidualPartition
end SensitivityMarkerResidualPartition
namespace SensitivityOperativeHeads
end SensitivityOperativeHeads
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction



/-! Actual socket heads give a bounded finite partition model. It preserves
the refined incoming counts and both the raw and compressed converted
incidence counts. -/
namespace SensitivityActualMacroPartition

noncomputable section
open scoped Classical BigOperators
open SensitivityFiniteHeadReindexing SensitivityMacroPartitionModel
open SensitivityRankedConstruction SensitivityGuardEvents SensitivityHighHeadGuardBridge
open SensitivityIndexedGuardResiduals SensitivityOperativeHeads SensitivityMarkerResidualPartition
open SensitivityMacroConvertedIncidences
set_option autoImplicit false
set_option maxHeartbeats 700000

variable {n L : ℕ} {M B I Color : Type}

def indexedPartition (head : Fin n → M × B) : Partition n := representative (fun i => (head i).1)

def indexedArc (head : Fin n → M × B) (arc : (M × B) → (M × B) → Prop) : Fin n → Fin n → Prop :=
  fun i j => arc (head i) (head j)











def indexedResidual (head : Fin n → M × B) (count : (M × B) → ℕ)
    (arc : (M × B) → (M × B) → Prop) (i : Fin n) : ℕ :=
  count (head i) - (Finset.univ.filter (indexedArc head arc i)).card

def actualCounts [Fintype M] [Fintype B]
    (row : RowFamily I Color L) (head : Fin n → M × B) (macroArc : M → M → Prop)
    (label : M → M → Bool) (G low : Finset (M × B)) (cutoff : ℕ)
    (x : (((M × B) × Bool) × I) → Bool) : Fin n → ℕ :=
  clusterCounts (fun i => (head i).1) (indexedSet head G)
    (fun m => (commonDestinations row macroArc label low cutoff x m).card)

















end
end SensitivityActualMacroPartition


