-- Prove2me | Definitions.Def_Sensitivity213303_ActualNegativeBound
-- name    : Sensitivity213303_ActualNegativeBound
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-25T22:26:48.225292+00:00
-- url     : https://prove2.me/theorems/cc2f55cd-3906-469b-a90d-ad19f3a972e9
-- title:
--   The numerical expression for negative-target repair costs
-- statement:
--   negativeExpr sums over all failure levels k up to the strong tolerance. Its k-th term is the record-derived bound negativeCount(caps,q,r,k) multiplied by the child A expression from the strong guard to the strong target threshold at k. This is the arithmetic counterpart of the actual tier-weighted negative-target repair bound.
-- source:
--   Original Lean formalization for the Prove2Me block-sensitivity-versus-sensitivity campaign, module ActualNegativeBound; source SHA256 4afbf5cf56d05f9b385717e11ba7ffcaccea8defccc630bd6537c882535bfb00.

import Definitions.Def_Sensitivity213303_ActualCapPrefix
import Definitions.Def_Sensitivity213303_ActualKindFilters
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
namespace ThreeBoundNegativeGreedy
end ThreeBoundNegativeGreedy
namespace ThreeBoundNumeric
end ThreeBoundNumeric
namespace ThreeBoundNumericOrder
end ThreeBoundNumericOrder
namespace ThreeBoundProfiles
end ThreeBoundProfiles
namespace ThreeBoundWitness
end ThreeBoundWitness


set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 10000

namespace ThreeBoundActualNegativeBound
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundGradedCandidates
open ThreeBoundGradedCover ThreeBoundActualTargets ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundHeadExpressions ThreeBoundNumericOrder ThreeBoundNegativeGreedy
open scoped Classical BigOperators
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]

def negativeExpr (n : ℕ) (caps : Caps) (c : Entry) (r : Q2Record) : Expr n :=
  Expr.sum ((List.range (c.tolerance+1)).map fun k =>
    negativeCount caps c.tolerance r k * aExpr n c.guard (c.threshold k))





end
end ThreeBoundActualNegativeBound


