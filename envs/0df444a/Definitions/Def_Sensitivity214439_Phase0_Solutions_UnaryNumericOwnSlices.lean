-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_UnaryNumericOwnSlices
-- name    : Sensitivity214439_Phase0_Solutions_UnaryNumericOwnSlices
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T18:39:43.742795+00:00
-- url     : https://prove2.me/theorems/1103940d-0404-4613-801f-0cdc68fb664e
-- title:
--   Needed ranks and own promotion prices for unary strict states
-- statement:
--   For a strict unary recipe and weighted failure count $f$, define the needed rank by
--   $$
--   \operatorname{needed}(j,f)=
--   \begin{cases}12,&f>1,\\\ell_j(f),&f\le1.\end{cases}
--   $$
--   The value $12$ is an unattainable sentinel. With old child height $h$, the own promotion price is $A(h,\operatorname{needed})$ when $h\le\operatorname{needed}<12$, and zero otherwise.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/UnaryNumericOwnSlices.lean lines 19–23; SHA256 b02748fb30bab6ce64132a1c999fa30641dced5c53bf0d8644109ac97a53970b; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_LocalNumericRecurrence
import Definitions.Def_Sensitivity214439_Phase0_Solutions_LocalNumericSemanticBridge
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
namespace SensitivityNumericOwnFees
end SensitivityNumericOwnFees
namespace SensitivityOwnNaturalFees
end SensitivityOwnNaturalFees
namespace SensitivityOwnTargetBounds
end SensitivityOwnTargetBounds
namespace SensitivityProfile456
end SensitivityProfile456
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction
namespace SensitivityStrictGateStates
end SensitivityStrictGateStates
namespace SensitivityUnaryLocalNumericSemantics
end SensitivityUnaryLocalNumericSemantics
namespace SensitivityUnaryNumericOwnSlices
end SensitivityUnaryNumericOwnSlices



/-! Actual own-child promotion and joint events for the one-socket recurrence. -/
namespace SensitivityUnaryNumericOwnSlices

noncomputable section
open scoped Classical
open SensitivityRankedConstruction SensitivityProfile456 SensitivityJointEvents
open SensitivityGuardEvents SensitivityFiniteRanks SensitivityStrictGateStates
open SensitivityLocalConfigurationCoverage SensitivityNaturalTargetNeeds
open SensitivityOwnTargetBounds SensitivityOwnNaturalFees
open SensitivityLocalNumericSemantics SensitivityNumericOwnFees
open SensitivityUnaryLocalNumericSemantics
set_option autoImplicit false

variable {V I Color : Type}

def unaryNeeded (r : NumericRecipe) (j : Fin 12) (failures : ℕ) : ℕ :=
  if 1 < failures then 12 else (r.lo j failures).val

def unaryPromotionFee (v : NumericBounds) (old needed : ℕ) : ℕ :=
  if old ≤ needed ∧ needed < 12 then SensitivityLocalNumeric.entry v.profile 0 old needed else 0



















end
end SensitivityUnaryNumericOwnSlices


