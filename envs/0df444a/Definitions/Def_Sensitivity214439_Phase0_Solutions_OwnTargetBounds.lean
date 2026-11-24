-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_OwnTargetBounds
-- name    : Sensitivity214439_Phase0_Solutions_OwnTargetBounds
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T18:28:00.624031+00:00
-- url     : https://prove2.me/theorems/b2ad1bd4-409f-4a4a-905e-444d11720e2e
-- title:
--   Legal guard states and own-target joint slices
-- statement:
--   A guard state is legal for a row at rank $j$ when its soft active-check count is within the allowance and every hard check is inactive:
--   $$
--   C_{s_j}(v,x)\le q_j
--   \quad\land\quad
--   \forall Q\in\mathcal G_v,\ \neg\operatorname{active}_{h_j}(Q,x).
--   $$
--   The own joint-event set for side $s$ is the set of child coordinates whose lifted flip belongs to the union of the parent row's weak losses and strong gains.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/OwnTargetBounds.lean lines 16–71; SHA256 101c0e2eaf599ad14a112fbe97436d6bedf48a8bb92aafc7b0913ab5c526ba3f; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_JointEvents
import Definitions.Def_Sensitivity214439_Phase0_Solutions_RankedBooleanConstruction
import Definitions.Def_Sensitivity214439_Phase0_Solutions_SocketGateConstruction
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

namespace SensitivityFiniteRanks
end SensitivityFiniteRanks
namespace SensitivityGuardEvents
end SensitivityGuardEvents
namespace SensitivityJointEvents
end SensitivityJointEvents
namespace SensitivityOwnTargetBounds
end SensitivityOwnTargetBounds
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



/-! Own-target event slices of actual paired and unary gates. -/
namespace SensitivityOwnTargetBounds

noncomputable section
open scoped Classical
open SensitivityRankedConstruction SensitivityProfile456 SensitivityJointEvents
open SensitivityGuardEvents SensitivityFiniteRanks SensitivityStrictGateStates
open SensitivityTargetEvents SensitivitySocketEventSupport
set_option autoImplicit false

variable {V S I Color : Type} {L core : ℕ}

def LegalGuards (row : RowFamily I Color L) (guards : GuardFamily V S)
    (recipe : GateRecipe S L) (v : V) (j : Fin L) (x : ((V × S) × I) → Bool) : Prop :=
  guardCount row guards v (recipe.soft j) x ≤ recipe.allowance j ∧
    ∀ check ∈ guards v, ¬ guardActive row (recipe.hard j) x check







def ownJointEvents [Fintype V] [Fintype S] [Fintype I]
    (row : RowFamily I Color L) (guards : GuardFamily V S) (recipe : GateRecipe S L)
    (v : V) (weak strong : Fin L) (x : ((V × S) × I) → Bool) (s : S) : Finset I :=
  Finset.univ.filter fun i => ((v,s),i) ∈ jointEvents (gateRow row guards recipe) v weak strong x














end
end SensitivityOwnTargetBounds


