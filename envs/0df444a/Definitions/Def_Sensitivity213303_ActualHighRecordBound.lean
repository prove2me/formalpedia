-- Prove2me | Definitions.Def_Sensitivity213303_ActualHighRecordBound
-- name    : Sensitivity213303_ActualHighRecordBound
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-25T22:24:51.367606+00:00
-- url     : https://prove2.me/theorems/0eb4d01f-206e-44b8-a47c-c41c80863cf6
-- title:
--   The histogram expression for total high-head repair cost
-- statement:
--   For a weak/strong entry pair and exact record r, highExpr sums over the eight kinds. It charges every head its zero-hit cost, adds the one-hit increment for heads with one incoming guard source, and adds the two-hit increment for heads with at least two sources. The histogram fields are r(9+2t) and r(10+2t), and each increment uses natural-number subtraction. The semantic head-cost and monotonicity lemmas show that this expression bounds the union of repairs at all high heads.
-- source:
--   Original Lean formalization for the Prove2Me block-sensitivity-versus-sensitivity campaign, module ActualHighRecordBound; source SHA256 a788f758a8df0c9aa437911ba5cbdfd0bed7ee6207c4a4de779231f1f3121240.

/- The high-head and external-arc parts of the exact record cost bound actual
   parent flip sets, with no semantic transfer assumption. -/
import Definitions.Def_Sensitivity213303_ActualKindFilters
import Definitions.Def_Sensitivity213303_CandidateCoherence
import Definitions.Def_Sensitivity213303_FullProfileClosure
import Definitions.Def_Sensitivity213303_GlobalAccounting
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
import Definitions.Def_Sensitivity213303_Q2EnumerationBridge
import Definitions.Def_Sensitivity213303_Q2RawExpressions
import Definitions.Def_Sensitivity213303_Q2RecordFields
import Definitions.Def_Sensitivity213303_RecursiveLowerBounds
import Definitions.Def_Sensitivity213303_ResidualCaps
import Definitions.Def_Sensitivity213303_TournamentHighRows
import Definitions.Def_Sensitivity213303_WitnessLifting
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
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
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
namespace OAI.Paper320
end OAI.Paper320
namespace ThreeBoundActualHeadCosts
end ThreeBoundActualHeadCosts
namespace ThreeBoundActualRecordFields
end ThreeBoundActualRecordFields
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
namespace ThreeBoundHeadCostOrder
end ThreeBoundHeadCostOrder
namespace ThreeBoundHeadExpressions
end ThreeBoundHeadExpressions
namespace ThreeBoundNumeric
end ThreeBoundNumeric
namespace ThreeBoundPositive
end ThreeBoundPositive
namespace ThreeBoundProfiles
end ThreeBoundProfiles
namespace ThreeBoundQ2
end ThreeBoundQ2
namespace ThreeBoundWitness
end ThreeBoundWitness


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

namespace ThreeBoundHighRecordBound
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundHeadCharge ThreeBoundGradedCandidates ThreeBoundGradedCover ThreeBoundActualHeadCosts
open ThreeBoundHeadExpressions ThreeBoundAllKindHeadCosts ThreeBoundActualRecordFields
open ThreeBoundHeadCostOrder ThreeBoundNumeric ThreeBoundFullProfile ThreeBoundQ2
open scoped Classical BigOperators
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]

def highExpr (n : ℕ) (a c : Entry) (r : Q2Record) : Expr n :=
  Expr.sum ((List.range 8).map fun t =>
    r t * headCost n a c t 0 +
    r (9+2*t) * (headCost n a c t 1-headCost n a c t 0) +
    r (10+2*t) * (headCost n a c t 2-headCost n a c t 0))













end
end ThreeBoundHighRecordBound


