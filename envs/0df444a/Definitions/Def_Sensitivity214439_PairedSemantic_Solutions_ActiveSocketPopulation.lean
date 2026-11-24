-- Prove2me | Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_ActiveSocketPopulation
-- name    : Sensitivity214439_PairedSemantic_Solutions_ActiveSocketPopulation
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T20:33:30.617399+00:00
-- url     : https://prove2.me/theorems/ecd52ffb-680c-4a04-a07c-170c14df976c
-- title:
--   Conflict graphs on finite candidate sets
-- statement:
--   Define the simple conflict graph on physical rows using the symmetric, irreflexive active-side conflict relation. For a finite candidate set $S$, its candidate graph is the graph induced on the subtype of rows belonging to $S$. This retains the exact conflict relation while giving the finite vertex type used by edge-count and independence inequalities.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/ActiveSocketPopulation.lean lines 16–24; SHA256 6e8333efc3b9b8eb8680beb3bc94111319da777a6d0eb3c7e01c963dc419e611; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_ActiveSocketMacroGeometry
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
namespace SensitivityPseudoforest
end SensitivityPseudoforest
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction



/-! Population inequalities with actual positive-socket and guard-count premises. -/
namespace SensitivityActiveSocketPopulation

noncomputable section
open scoped Classical BigOperators
open SensitivityRankedConstruction SensitivityHighHeadGuardBridge
open SensitivityActiveSocketGeometry SensitivityGraphPopulation SensitivityPseudoforest
set_option autoImplicit false

variable {V M B I Color : Type} {L : ℕ}

def conflictGraph (arc : M → M → Prop) (label : M → M → Bool)
    (active : M × B → Bool) : SimpleGraph (M × B) where
  Adj := Conflict arc label active
  symm := ⟨fun _ _ => conflict_symm⟩
  loopless := ⟨conflict_irrefl arc label active⟩

def candidateGraph (arc : M → M → Prop) (label : M → M → Bool)
    (active : M × B → Bool) (s : Finset (M × B)) : SimpleGraph s :=
  (conflictGraph arc label active).induce (↑s : Set (M × B))


















end
end SensitivityActiveSocketPopulation


