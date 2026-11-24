-- Prove2me | Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_MacroConvertedIncidences
-- name    : Sensitivity214439_PairedSemantic_Solutions_MacroConvertedIncidences
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T20:22:52.488097+00:00
-- url     : https://prove2.me/theorems/afb9b36d-83eb-46e9-b739-3ffca3fd1e8f
-- title:
--   Internal and shared external converted-destination indices
-- statement:
--   Defines commonDestinations for a source macro as the low destinations in another macro whose labeled child is active. compressedKeys pairs each guard-source macro with these shared destinations. internalConvertedEdges instead retains each source/destination pair in the same macro. Together they index the converted charge after repeated external incidences are compressed.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/MacroConvertedIncidences.lean lines 17–145; SHA256 24b28cd7d2787a85c228520330ec313de7c16d676acbb6a5d067793598aa23a6; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_HighHeadGuardBridge
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_IndexedGuardResiduals
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_MarkerResidualPartition
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_TournamentSocketGuards
import Definitions.Def_Sensitivity214439_Phase0_Solutions_RankedBooleanConstruction
import Definitions.Def_Sensitivity214439_Phase0_Solutions_SocketGateConstruction
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

namespace SensitivityGuardEvents
end SensitivityGuardEvents
namespace SensitivityHighHeadGuardBridge
end SensitivityHighHeadGuardBridge
namespace SensitivityIndexedGuardResiduals
end SensitivityIndexedGuardResiduals
namespace SensitivityMacroConvertedIncidences
end SensitivityMacroConvertedIncidences
namespace SensitivityMarkerResidualPartition
end SensitivityMarkerResidualPartition
namespace SensitivityOperativeHeads
end SensitivityOperativeHeads
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction



/-! Equal checks from one source macro have a common set of converted
external destinations. Its size is the `counts_u` variable used by the
finite guard partition, while the original incidence sum stays separate. -/
namespace SensitivityMacroConvertedIncidences

noncomputable section
open scoped Classical BigOperators
open SensitivityRankedConstruction SensitivityGuardEvents SensitivityHighHeadGuardBridge
open SensitivityIndexedGuardResiduals SensitivityOperativeHeads SensitivityMarkerResidualPartition
set_option autoImplicit false

variable {M B I Color : Type} {L : ℕ}

def commonDestinations [Fintype M] [Fintype B]
    (row : RowFamily I Color L) (macroArc : M → M → Prop) (label : M → M → Bool)
    (low : Finset (M × B)) (cutoff : ℕ) (x : (((M × B) × Bool) × I) → Bool)
    (m : M) : Finset (M × B) :=
  low.filter fun w => w.1 ≠ m ∧ macroArc m w.1 ∧
    passes row cutoff (socketInput x (w,label m w.1))











def compressedKeys [Fintype M] [Fintype B]
    (row : RowFamily I Color L) (macroArc : M → M → Prop) (label : M → M → Bool)
    (G low : Finset (M × B)) (cutoff : ℕ) (x : (((M × B) × Bool) × I) → Bool) :
    Finset (Σ _m : M, M × B) :=
  (G.image Prod.fst).sigma (commonDestinations row macroArc label low cutoff x)





def internalConvertedEdges [Fintype M] [Fintype B]
    (row : RowFamily I Color L) (macroArc : M → M → Prop)
    (label : M → M → Bool) (internalArc : B → B → Prop)
    (H G low : Finset (M × B)) (cutoff : ℕ) (x : (((M × B) × Bool) × I) → Bool) :
    Finset (Σ _v : M × B, M × B) :=
  G.sigma fun v => (converted
    (outsideDestinations row (pairedIndexing macroArc label internalArc) H v cutoff x) low).filter
      fun w => w.1 = v.1







end
end SensitivityMacroConvertedIncidences


