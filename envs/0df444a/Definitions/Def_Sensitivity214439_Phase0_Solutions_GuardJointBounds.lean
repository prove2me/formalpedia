-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_GuardJointBounds
-- name    : Sensitivity214439_Phase0_Solutions_GuardJointBounds
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T18:10:38.744405+00:00
-- url     : https://prove2.me/theorems/95d29629-db7d-4f5f-bb87-afc07e6bfde5
-- title:
--   Mixed upward and downward OR-guard events
-- statement:
--   For ranks $\ell,h$, input $x$, and check $Q$, define
--   $$
--   \operatorname{mixedGuardCoordinates}(\ell,h,Q,x)
--   =R_h(Q,x)\cup D_\ell(Q,x).
--   $$
--   This combines the two directions that occur in a joint guard interval: activation above the upper threshold and clearing below the lower threshold.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/GuardJointBounds.lean lines 14–17; SHA256 d2c7d656287f3c852636411fc0dc123c7a4f04dbf3613f623904cffb34a71b53; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_GuardEvents
import Definitions.Def_Sensitivity214439_Phase0_Solutions_RankedBooleanConstruction
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
namespace SensitivityGuardJointBounds
end SensitivityGuardJointBounds
namespace SensitivityJointEvents
end SensitivityJointEvents
namespace SensitivityProfile456
end SensitivityProfile456
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction
namespace SensitivityStrictGateStates
end SensitivityStrictGateStates



/-! Quantitative union bounds for upward/downward events of one OR guard. -/
namespace SensitivityGuardJointBounds

noncomputable section
open scoped Classical BigOperators
open SensitivityRankedConstruction SensitivityProfile456 SensitivityJointEvents
open SensitivityGuardEvents SensitivityFiniteRanks SensitivityStrictGateStates
set_option autoImplicit false

variable {V S I Color : Type} {L core : ℕ}

def mixedGuardCoordinates [Fintype V] [Fintype S] [Fintype I]
    (row : RowFamily I Color L) (low high : Fin L)
    (x : ((V × S) × I) → Bool) (check : Finset (V × S)) : Finset ((V × S) × I) :=
  risingCoordinates row high.val x check ∪ droppingCoordinates row low.val x check










end
end SensitivityGuardJointBounds


