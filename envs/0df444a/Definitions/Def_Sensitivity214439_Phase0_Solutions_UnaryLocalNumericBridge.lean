-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_UnaryLocalNumericBridge
-- name    : Sensitivity214439_Phase0_Solutions_UnaryLocalNumericBridge
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T18:39:39.847081+00:00
-- url     : https://prove2.me/theorems/8096f031-8c22-4553-8792-d8352357dbb5
-- title:
--   Unary local recipe conditions and duplicated height states
-- statement:
--   Unary local conditions require a strict recipe above a given core and anchor cutoff, recipe nesting, the strict guard shape at every rank above the core, and soft cutoffs below the number of ranks.
--
--   The actual unary state for the strict recurrence duplicates the one own-child height into both target fields and records the occupied guard-height list:
--   $$
--   s(x)=\bigl(h_F(x_v),h_F(x_v),\mathbf h_{\rm guards}\bigr).
--   $$
--   This embeds the one-target construction in the same finite state format used for matching paired targets.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/UnaryLocalNumericBridge.lean lines 16–33; SHA256 31d44ad1cbe2a1fd5bb377e1990b226ca39827901e86ed5b53af14220f09e37f; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_FiniteRanks
import Definitions.Def_Sensitivity214439_Phase0_Solutions_GateInvariants
import Definitions.Def_Sensitivity214439_Phase0_Solutions_LocalNumericRecurrence
import Definitions.Def_Sensitivity214439_Phase0_Solutions_LocalNumericSemanticBridge
import Definitions.Def_Sensitivity214439_Phase0_Solutions_RankedBooleanConstruction
import Definitions.Def_Sensitivity214439_Phase0_Solutions_SocketGateConstruction
import Definitions.Def_Sensitivity214439_Phase0_Solutions_StrictGateStates
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Range
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
namespace SensitivityLocalConfigurationCoverage
end SensitivityLocalConfigurationCoverage
namespace SensitivityLocalNumericSemantics
end SensitivityLocalNumericSemantics
namespace SensitivityNaturalTargetNeeds
end SensitivityNaturalTargetNeeds
namespace SensitivityProfile456
end SensitivityProfile456
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction
namespace SensitivityStrictGateStates
end SensitivityStrictGateStates
namespace SensitivityUnaryLocalNumericSemantics
end SensitivityUnaryLocalNumericSemantics



/-! Actual one-socket sources reach the finite unary numeric recurrence states. -/
namespace SensitivityUnaryLocalNumericSemantics

noncomputable section
open scoped Classical
open SensitivityRankedConstruction SensitivityProfile456 SensitivityJointEvents
open SensitivityGuardEvents SensitivityFiniteRanks SensitivityStrictGateStates
open SensitivityLocalConfigurationCoverage SensitivityNaturalTargetNeeds
open SensitivityLocalNumericSemantics
set_option autoImplicit false

variable {I Color V : Type} {L core : ℕ}

structure UnaryLocalConditions (soft hard allowance : Fin L → ℕ)
    (target : Fin L → ℕ → Fin L) (core : ℕ) (anchor : Fin L) : Prop where
  strict : StrictRecipe (unaryRecipe soft hard allowance target) core anchor.val
  nesting : RecipeNesting (unaryRecipe soft hard allowance target)
  shape : ∀ j, core ≤ j.val → StrictGuardShape (unaryRecipe soft hard allowance target) j
  soft_range : ∀ j, soft j < L



def unaryState (row : RowFamily I Color 12) (guards : GuardFamily V Unit)
    (v : V) (cutoff : Fin 12) (x : ((V × Unit) × I) → Bool) : NumericState :=
  ⟨rankHeight row (socketInput x (v,())),rankHeight row (socketInput x (v,())),
    occupiedGuardHeights row guards v cutoff x⟩













end
end SensitivityUnaryLocalNumericSemantics


