-- Prove2me | Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_MarkedPseudoforestPopulation
-- name    : Sensitivity214439_PairedSemantic_Solutions_MarkedPseudoforestPopulation
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T20:33:29.746686+00:00
-- url     : https://prove2.me/theorems/e11903c7-1539-41a1-ae87-4b4a1efae277
-- title:
--   Candidate sources of outgoing marker arcs
-- statement:
--   The marker-source set consists of candidates with at least one outgoing arc to the selected marker set. Under a candidate guard budget of one and passing high-marker sides, such a candidate spends its only possible guard on the marker and is consequently a sink of the candidate-conflict relation. This set supplies the additional sink count in marked pseudoforest inequalities.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/MarkedPseudoforestPopulation.lean lines 121–122; SHA256 1da888bf3cbf416836be7139ea98298c6664f21a2324b6b3845ef18ed6a4facc; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_MarkedSocketPopulation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Fin
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

namespace SensitivityActiveSocketGeometry
end SensitivityActiveSocketGeometry
namespace SensitivityActiveSocketPopulation
end SensitivityActiveSocketPopulation
namespace SensitivityHighHeadGuardBridge
end SensitivityHighHeadGuardBridge
namespace SensitivityMarkedPseudoforestPopulation
end SensitivityMarkedPseudoforestPopulation
namespace SensitivityMarkedSocketPopulation
end SensitivityMarkedSocketPopulation
namespace SensitivityPseudoforest
end SensitivityPseudoforest
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction



/-! The marked pseudoforest inequalities, including genuine marker-budget sinks. -/
namespace SensitivityMarkedPseudoforestPopulation

noncomputable section
open scoped Classical BigOperators
open SensitivityRankedConstruction SensitivityHighHeadGuardBridge
open SensitivityActiveSocketGeometry SensitivityActiveSocketPopulation
open SensitivityMarkedSocketPopulation SensitivityPseudoforest
set_option autoImplicit false

variable {V M B I Color : Type} {L : ℕ}









def markerSources (arc : V → V → Prop) (candidates markers : Finset V) : Finset V :=
  candidates.filter fun v => (toMarkers arc markers v).Nonempty











end
end SensitivityMarkedPseudoforestPopulation


