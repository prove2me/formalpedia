-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_UnaryGuardNumericSlices
-- name    : Sensitivity214439_Phase0_Solutions_UnaryGuardNumericSlices
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T18:51:59.21226+00:00
-- url     : https://prove2.me/theorems/1d83515b-d3e5-4380-ad28-c339044bf590
-- title:
--   Structural unary context and check-supported event slices
-- statement:
--   A unary guard context packages a nested child family, strict color uniqueness above core $5$, disjoint non-self guards, a numerical recipe marked unary with equal lower and upper targets, and the valid unary local conditions. It also fixes a child color accepted at core $5$ in the row's own socket.
--
--   For any finite parent event set $E$ and check $Q$, its guard slice is
--   $$
--   E|_Q=\{b\in E:\operatorname{socket}(b)\in Q\}.
--   $$
--   This keeps actual bit events together with the structural assumptions needed to price their occupied and cold guard slices.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/UnaryGuardNumericSlices.lean lines 18–31; SHA256 cb2b214a311339550d2ba67aa39c1bd1fb035f8baef5b63ee2ece70fe8ad5935; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_GuardEvents
import Definitions.Def_Sensitivity214439_Phase0_Solutions_LocalNumericRecurrence
import Definitions.Def_Sensitivity214439_Phase0_Solutions_LocalNumericSemanticBridge
import Definitions.Def_Sensitivity214439_Phase0_Solutions_RankedBooleanConstruction
import Definitions.Def_Sensitivity214439_Phase0_Solutions_SocketGateConstruction
import Definitions.Def_Sensitivity214439_Phase0_Solutions_UnaryLocalNumericBridge
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
namespace SensitivityGuardIntervalCertificates
end SensitivityGuardIntervalCertificates
namespace SensitivityJointEvents
end SensitivityJointEvents
namespace SensitivityLocalConfigurationCoverage
end SensitivityLocalConfigurationCoverage
namespace SensitivityLocalNumericSemantics
end SensitivityLocalNumericSemantics
namespace SensitivityNumericGuardFees
end SensitivityNumericGuardFees
namespace SensitivityProfile456
end SensitivityProfile456
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction
namespace SensitivityStrictGateStates
end SensitivityStrictGateStates
namespace SensitivityUnaryGuardNumericSlices
end SensitivityUnaryGuardNumericSlices
namespace SensitivityUnaryLocalNumericSemantics
end SensitivityUnaryLocalNumericSemantics



/-! Numeric interval certificates cover the actual one-socket guard slices. -/
namespace SensitivityUnaryGuardNumericSlices

noncomputable section
open scoped Classical
open SensitivityRankedConstruction SensitivityProfile456 SensitivityJointEvents
open SensitivityGuardEvents SensitivityFiniteRanks SensitivityStrictGateStates
open SensitivityLocalConfigurationCoverage SensitivityGuardIntervalCertificates
open SensitivityLocalNumericSemantics SensitivityNumericGuardFees
open SensitivityUnaryLocalNumericSemantics
set_option autoImplicit false

variable {V I Color : Type}

structure UnaryContext (row : RowFamily I Color 12) (guards : GuardFamily V Unit)
    (r : NumericRecipe) (allowance : Fin 12 → ℕ) (v : V) (x : ((V × Unit) × I) → Bool) where
  nested : Nested row
  unique : StrictUnique row 5
  noSelf : NoSelfGuards guards
  disjoint : DisjointChecks guards
  unary : r.unary = true
  diagonal : ∀ j f, r.hi j f = r.lo j f
  conditions : UnaryLocalConditions r.soft r.hard allowance r.lo 5 (5 : Fin 12)
  color : Color
  anchor : row color (5 : Fin 12) (socketInput x (v,()))

def guardSlice (E : Finset ((V × Unit) × I)) (check : Finset (V × Unit)) : Finset ((V × Unit) × I) :=
  E.filter fun bit => bit.1 ∈ check

variable {row : RowFamily I Color 12} {guards : GuardFamily V Unit}
  {r : NumericRecipe} {allowance : Fin 12 → ℕ} {v : V} {x : ((V × Unit) × I) → Bool}




























end
end SensitivityUnaryGuardNumericSlices


