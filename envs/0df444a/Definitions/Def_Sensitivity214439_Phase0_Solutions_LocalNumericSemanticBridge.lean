-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_LocalNumericSemanticBridge
-- name    : Sensitivity214439_Phase0_Solutions_LocalNumericSemanticBridge
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T18:27:41.611284+00:00
-- url     : https://prove2.me/theorems/6432b969-c571-4bbf-af10-d8c8869b4869
-- title:
--   Real profile interpretation of numerical bounds
-- statement:
--   The numerical recipe, state, and bounds names abbreviate their finite recurrence types. A numerical profile array is interpreted as a real-valued profile using the fixed 456-coordinate index map. For a real scale $\sigma$, define
--   $$
--   (\sigma p)(q)=\sigma p(q),\qquad
--   P_\sigma(a,n)=\sigma P(a,n),\qquad
--   J_\sigma(w,a,n)=\sigma J(w,a,n).
--   $$
--   The natural-number data are cast to reals before scaling; no positivity condition is part of these definitions themselves.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/LocalNumericSemanticBridge.lean lines 18–32; SHA256 af8520e8dba5de829cc4f1c1cbee8cbe32fc38c9d42d893bb337a06cf6445f9c; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_LocalNumericRecurrence
import Definitions.Def_Sensitivity214439_Phase0_Solutions_Profile456
import Definitions.Def_Sensitivity214439_Phase0_Solutions_ProfileIndexing
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



/-!
The finite numeric states are reached from actual Boolean gate inputs. The
literal array ordering is connected to the four triangular profile fields.
-/
namespace SensitivityLocalNumericSemantics

noncomputable section
open scoped Classical
open SensitivityRankedConstruction SensitivityProfile456 SensitivityJointEvents
open SensitivityGuardEvents SensitivityFiniteRanks SensitivityStrictGateStates
open SensitivityLocalConfigurationCoverage SensitivityNaturalTargetNeeds
set_option autoImplicit false

abbrev NumericRecipe := SensitivityLocalNumeric.Recipe
abbrev NumericState := SensitivityLocalNumeric.State
abbrev NumericBounds := SensitivityLocalNumeric.Bounds

def numericProfile (v : NumericBounds) : Profile 12 :=
  SensitivityProfileIndexing.fromFlat fun i => (v.profile[i.val]?.getD 0 : ℝ)

def scaledProfile (scale : ℝ) (v : NumericBounds) : Profile 12 :=
  fun q => scale * numericProfile v q

def scaledPromotion (scale : ℝ) (v : NumericBounds) (a n : Fin 12) : ℝ :=
  scale * v.promotion a.val n.val

def scaledJoint (scale : ℝ) (v : NumericBounds) (c a n : Fin 12) : ℝ :=
  scale * v.joint c.val a.val n.val












































end
end SensitivityLocalNumericSemantics


