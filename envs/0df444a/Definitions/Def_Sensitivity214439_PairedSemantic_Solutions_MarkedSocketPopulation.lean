-- Prove2me | Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_MarkedSocketPopulation
-- name    : Sensitivity214439_PairedSemantic_Solutions_MarkedSocketPopulation
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T20:22:50.440085+00:00
-- url     : https://prove2.me/theorems/9eaf2689-a709-45c0-92d7-c8dec8773b77
-- title:
--   Clean, failed, and reverse marker incidences
-- statement:
--   For a source row, its outgoing marker set consists of the selected markers reached by its paired arcs. Relative to a marker, clean candidates are reached destinations whose corresponding guard check is inactive, and failed candidates are reached destinations whose check is active.
--
--   The general indexed-guard bound counts any finite set of distinct active destinations by the source's actual active-guard count. This is the common counting principle for candidate conflicts, high-marker arcs, and residual failed incidences.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/MarkedSocketPopulation.lean lines 15–43; SHA256 e054fe8e5123006085f22ef85c964ee16ac1d1a382c0d022de446fcd82af7807; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_HighHeadGuardBridge
import Definitions.Def_Sensitivity214439_Phase0_Solutions_HighHeadGuardBridge
import Definitions.Def_Sensitivity214439_Phase0_Solutions_RankedBooleanConstruction
import Definitions.Def_Sensitivity214439_Phase0_Solutions_SocketGateConstruction
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
namespace SensitivityGraphPopulation
end SensitivityGraphPopulation
namespace SensitivityHighHeadGuardBridge
end SensitivityHighHeadGuardBridge
namespace SensitivityMarkedSocketPopulation
end SensitivityMarkedSocketPopulation
namespace SensitivityPseudoforest
end SensitivityPseudoforest
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction



/-! Exact marker incidences and clean dominated candidate populations. -/
namespace SensitivityMarkedSocketPopulation

noncomputable section
open scoped Classical BigOperators
open SensitivityRankedConstruction SensitivityHighHeadGuardBridge
open SensitivityActiveSocketGeometry SensitivityActiveSocketPopulation
open SensitivityGraphPopulation SensitivityPseudoforest
set_option autoImplicit false

variable {V S M B I Color : Type} {L : ℕ}

theorem positive_destinations_le_guardCount
    (row : RowFamily I Color L) {guards : GuardFamily V S} {arc : V → V → Prop}
    (idx : GuardIndexing guards arc) (destinations : Finset V) (v : V) (cutoff : ℕ)
    (x : ((V × S) × I) → Bool)
    (hgood : ∀ w ∈ destinations, arc v w ∧ guardActive row cutoff x (idx.check v w)) :
    destinations.card ≤ guardCount row guards v cutoff x := by
  unfold guardCount
  apply Finset.card_le_card_of_injOn (idx.check v)
  · intro w hw
    exact Finset.mem_filter.mpr ⟨idx.member v w (hgood w hw).1, (hgood w hw).2⟩
  · intro w hw z hz heq
    obtain ⟨socket, hs⟩ := idx.nonempty v w (hgood w hw).1
    have hzs : socket ∈ idx.check v z := heq ▸ hs
    exact (idx.destination v w socket hs).symm.trans (idx.destination v z socket hzs)

def toMarkers (arc : V → V → Prop) (markers : Finset V) (v : V) : Finset V :=
  markers.filter (arc v)

def cleanCandidates (row : RowFamily I Color L) (macroArc : M → M → Prop)
    (label : M → M → Bool) (internalArc : B → B → Prop) (candidates : Finset (M × B))
    (cutoff : ℕ) (x : (((M × B) × Bool) × I) → Bool) (marker : M × B) : Finset (M × B) :=
  candidates.filter fun v => pairedArc macroArc internalArc marker v ∧
    ¬ guardActive row cutoff x (pairedCheck label marker v)

def failedIntoCandidates (row : RowFamily I Color L) (macroArc : M → M → Prop)
    (label : M → M → Bool) (internalArc : B → B → Prop) (candidates : Finset (M × B))
    (cutoff : ℕ) (x : (((M × B) × Bool) × I) → Bool) (marker : M × B) : Finset (M × B) :=
  candidates.filter fun v => pairedArc macroArc internalArc marker v ∧
    guardActive row cutoff x (pairedCheck label marker v)




























end
end SensitivityMarkedSocketPopulation


