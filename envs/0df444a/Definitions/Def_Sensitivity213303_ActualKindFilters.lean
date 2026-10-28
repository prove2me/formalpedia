-- Prove2me | Definitions.Def_Sensitivity213303_ActualKindFilters
-- name    : Sensitivity213303_ActualKindFilters
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-25T22:23:47.869312+00:00
-- url     : https://prove2.me/theorems/53991418-cef8-40a4-99b1-ffc25d38c509
-- title:
--   The guard-branch index associated with a candidate kind
-- statement:
--   For one of the eight q≤2 kinds, guardLevel(k) equals k−3 when k≤5 and k−6 otherwise, with natural-number subtraction. On the guard-bearing kinds 3, 4, 5, 6, 7 this gives branch indices 0, 1, 2, 0, 1 respectively. This index selects the precise weak/strong threshold comparison in the recipe-dependent feasibility filter.
-- source:
--   Original Lean formalization for the Prove2Me block-sensitivity-versus-sensitivity campaign, module ActualKindFilters; source SHA256 598b6c51ded9802b69c6a5a16a7156e5bb0257892c4b379809994981b3c297a0.

/- Actual candidates satisfy every recipe-dependent q2 record filter. -/
import Definitions.Def_Sensitivity213303_CandidateCoherence
import Definitions.Def_Sensitivity213303_FullProfileClosure
import Definitions.Def_Sensitivity213303_GradedCandidates
import Definitions.Def_Sensitivity213303_GradedGlobalCover
import Definitions.Def_Sensitivity213303_GradedPositiveBoundary
import Definitions.Def_Sensitivity213303_GuardAugmentation
import Definitions.Def_Sensitivity213303_HeadCostExpressions
import Definitions.Def_Sensitivity213303_HeadCosts
import Definitions.Def_Sensitivity213303_NumericExpressions
import Definitions.Def_Sensitivity213303_ProfileClosures
import Definitions.Def_Sensitivity213303_Q2CandidateTypes
import Definitions.Def_Sensitivity213303_Q2Enumeration
import Definitions.Def_Sensitivity213303_Q2RawExpressions
import Definitions.Def_Sensitivity213303_RecursiveLowerBounds
import Definitions.Def_Sensitivity213303_TournamentHighRows
import Definitions.Def_Sensitivity213303_WitnessLifting
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
namespace OAI.Paper320
end OAI.Paper320
namespace ThreeBoundActualHeadCosts
end ThreeBoundActualHeadCosts
namespace ThreeBoundAllKindHeadCosts
end ThreeBoundAllKindHeadCosts
namespace ThreeBoundFullProfile
end ThreeBoundFullProfile
namespace ThreeBoundGradedCandidates
end ThreeBoundGradedCandidates
namespace ThreeBoundGradedCover
end ThreeBoundGradedCover
namespace ThreeBoundHeadCharge
end ThreeBoundHeadCharge
namespace ThreeBoundHeadExpressions
end ThreeBoundHeadExpressions
namespace ThreeBoundNumeric
end ThreeBoundNumeric
namespace ThreeBoundPositive
end ThreeBoundPositive
namespace ThreeBoundProfiles
end ThreeBoundProfiles
namespace ThreeBoundWitness
end ThreeBoundWitness


set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace ThreeBoundActualKindFilters
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundHeadCharge ThreeBoundGradedCandidates ThreeBoundGradedCover ThreeBoundActualHeadCosts
open ThreeBoundHeadExpressions ThreeBoundAllKindHeadCosts ThreeBoundNumeric ThreeBoundFullProfile
open scoped Classical
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]

def guardLevel (kind : Fin 8) : ℕ := if kind.val ≤ 5 then kind.val-3 else kind.val-6











end
end ThreeBoundActualKindFilters


