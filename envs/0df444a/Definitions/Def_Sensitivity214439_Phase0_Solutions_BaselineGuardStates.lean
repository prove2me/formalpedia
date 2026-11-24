-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_BaselineGuardStates
-- name    : Sensitivity214439_Phase0_Solutions_BaselineGuardStates
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T12:36:13.074864+00:00
-- url     : https://prove2.me/theorems/bc9b5036-57d2-42fb-953a-0dbe7b9bed26
-- title:
--   Occupancy updates and scalar paired acceptance
-- statement:
--   For a cutoff $a$ and height $h$, define the occupancy indicator $\mathbf1_{a<h}$. Replacing one guard height $h$ by $h'$ updates a total count $C$ to
--   $$
--   C-\mathbf1_{a<h}+\mathbf1_{a<h'}.
--   $$
--   Given a rank-dependent allowance $q_j$ and target ranks $\ell_j(f),u_j(f)$, scalar paired acceptance of child heights $h_0,h_1$ means
--   $$
--   f\le q_j,\qquad g=0,\qquad
--   \ell_j(f)<\min(h_0,h_1),\qquad
--   u_j(f)<\max(h_0,h_1),
--   $$
--   where $f$ and $g$ are the soft and hard active-check counts. The finite scalar acceptance predicate has a decidable instance.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/BaselineGuardStates.lean lines 15–60; SHA256 0da82bac6e357e8d47d3be015a5a50472edccce858af614512103c22b7ff4107; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SensitivityBaselineGuardStates
end SensitivityBaselineGuardStates
namespace SensitivityFiniteRanks
end SensitivityFiniteRanks
namespace SensitivityGuardEvents
end SensitivityGuardEvents
namespace SensitivityProfile456
end SensitivityProfile456
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction
namespace SensitivitySocketEventSupport
end SensitivitySocketEventSupport
namespace SensitivityStrictGateStates
end SensitivityStrictGateStates
namespace SensitivityTargetEvents
end SensitivityTargetEvents



/-! Full soft/hard count semantics for guard changes at every rank, including
the loose rows whose allowance exceeds one. -/
namespace SensitivityBaselineGuardStates

noncomputable section
open scoped Classical BigOperators
open SensitivityRankedConstruction SensitivityProfile456 SensitivityGuardEvents
open SensitivityFiniteRanks SensitivityStrictGateStates SensitivityTargetEvents
open SensitivitySocketEventSupport

variable {V S I Color : Type} {L core : ℕ}

def occupied (cutoff height : ℕ) : ℕ := if cutoff < height then 1 else 0

def updatedCount (cutoff total old fresh : ℕ) : ℕ :=
  total - occupied cutoff old + occupied cutoff fresh



def pairedCountAccepts (allowance : Fin L → ℕ) (lo hi : Fin L → ℕ → Fin L)
    (j : Fin L) (softCount hardCount left right : ℕ) : Prop :=
  softCount ≤ allowance j ∧ hardCount = 0 ∧
    (lo j softCount).val < min left right ∧ (hi j softCount).val < max left right

instance (allowance : Fin L → ℕ) (lo hi : Fin L → ℕ → Fin L)
    (j : Fin L) (softCount hardCount left right : ℕ) :
    Decidable (pairedCountAccepts allowance lo hi j softCount hardCount left right) := by
  unfold pairedCountAccepts
  infer_instance













end
end SensitivityBaselineGuardStates


