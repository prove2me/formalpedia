-- Prove2me | Definitions.Def_Sensitivity213303_ActualQ2Bound
-- name    : Sensitivity213303_ActualQ2Bound
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-25T22:28:54.468587+00:00
-- url     : https://prove2.me/theorems/937d5bf4-afdb-472e-9f44-8439b579e6ca
-- title:
--   The maximum exact-record expression for a graded upward transition
-- statement:
--   gradedAExpr takes the maximum of recordCost over all rows of a supplied finite record table that pass recordAllowedFor for the given cap table and weak/strong recipe entries. Each accepted row contributes its complete high-head, negative-target and external-guard cost. Once every actual head configuration is represented and its record passes the feasibility filters, this finite maximum is an upper bound for the actual parent A transition.
-- source:
--   Original Lean formalization for the Prove2Me block-sensitivity-versus-sensitivity campaign, module ActualQ2Bound; source SHA256 d2cf219a92dd2bd54c7f2d711d4a10d4b0930d23b66d6c4b074fb7fbacbc612f.

/- Complete semantic proof of the q2 record-maximum upward bound. -/
import Definitions.Def_Sensitivity213303_ActualCapPrefix
import Definitions.Def_Sensitivity213303_ActualHighRecordBound
import Definitions.Def_Sensitivity213303_ActualKindFilters
import Definitions.Def_Sensitivity213303_ActualNegativeBound
import Definitions.Def_Sensitivity213303_ActualPrefixCaps
import Definitions.Def_Sensitivity213303_ActualResidualCaps
import Definitions.Def_Sensitivity213303_ActualTargetAccounting
import Definitions.Def_Sensitivity213303_CandidateCoherence
import Definitions.Def_Sensitivity213303_CapAlgorithm
import Definitions.Def_Sensitivity213303_ClosureHomogeneity
import Definitions.Def_Sensitivity213303_FlatProfiles
import Definitions.Def_Sensitivity213303_FullProfileClosure
import Definitions.Def_Sensitivity213303_GlobalAccounting
import Definitions.Def_Sensitivity213303_GradedCandidates
import Definitions.Def_Sensitivity213303_GradedGlobalCover
import Definitions.Def_Sensitivity213303_GradedPositiveBoundary
import Definitions.Def_Sensitivity213303_GuardAugmentation
import Definitions.Def_Sensitivity213303_HeadCostExpressions
import Definitions.Def_Sensitivity213303_HeadCosts
import Definitions.Def_Sensitivity213303_NumericAdmissibility
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
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
namespace OAI.Paper320
end OAI.Paper320
namespace ThreeBoundActualCaps
end ThreeBoundActualCaps
namespace ThreeBoundActualEnumeration
end ThreeBoundActualEnumeration
namespace ThreeBoundActualNegativeBound
end ThreeBoundActualNegativeBound
namespace ThreeBoundActualRecordAllowed
end ThreeBoundActualRecordAllowed
namespace ThreeBoundActualRecordFields
end ThreeBoundActualRecordFields
namespace ThreeBoundActualTargets
end ThreeBoundActualTargets
namespace ThreeBoundFullProfile
end ThreeBoundFullProfile
namespace ThreeBoundGradedCandidates
end ThreeBoundGradedCandidates
namespace ThreeBoundGradedCover
end ThreeBoundGradedCover
namespace ThreeBoundHeadExpressions
end ThreeBoundHeadExpressions
namespace ThreeBoundHighRecordBound
end ThreeBoundHighRecordBound
namespace ThreeBoundNumeric
end ThreeBoundNumeric
namespace ThreeBoundProfiles
end ThreeBoundProfiles
namespace ThreeBoundRecordCaps
end ThreeBoundRecordCaps
namespace ThreeBoundTagPrefixes
end ThreeBoundTagPrefixes
namespace ThreeBoundWitness
end ThreeBoundWitness


set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace ThreeBoundActualQ2Bound
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundGradedCandidates
open ThreeBoundGradedCover ThreeBoundActualTargets ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundHeadExpressions ThreeBoundActualEnumeration ThreeBoundActualRecordFields
open ThreeBoundActualCaps ThreeBoundRecordCaps ThreeBoundTagPrefixes
open ThreeBoundActualRecordAllowed ThreeBoundActualNegativeBound ThreeBoundHighRecordBound
open scoped Classical BigOperators
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]

def gradedAExpr (n : ℕ) (caps : Caps) (records : List (List ℕ)) (a c : Entry) : Expr n :=
  Expr.maximum (records.filterMap fun xs =>
    let r := recordOfList xs
    if recordAllowedFor caps a c r then some (recordCost n caps a c r) else none)





end
end ThreeBoundActualQ2Bound


