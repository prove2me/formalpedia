-- Prove2me | Definitions.Def_Sensitivity213303_ActualCapPrefix
-- name    : Sensitivity213303_ActualCapPrefix
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-25T22:25:38.201977+00:00
-- url     : https://prove2.me/theorems/b0e0d553-3ec9-475b-8401-2140c478ddef
-- title:
--   Semantic validity of the q≤2 numerical cap table
-- statement:
--   CapsSound requires the labeling exclusions represented by a numerical Caps object: ordinary thresholds for q≤2, one-marker and two-marker dominator bounds, marked bounds with one or two markers at levels 1 and 2, and zero-mismatch marked bounds with three or four markers. It also includes positivity of the latter two thresholds. This proposition is the explicit contract connecting numerical prefix-cap formulas to proved combinatorial exclusions.
-- source:
--   Original Lean formalization for the Prove2Me block-sensitivity-versus-sensitivity campaign, module ActualCapPrefix; source SHA256 54a31c537548cc4ea9f8b1fbb7d176c8c76303c01efa8aa278e4c25202486d62.

/- All numerical prefix constraints hold for the actual candidate record. -/
import Definitions.Def_Sensitivity213303_ActualKindFilters
import Definitions.Def_Sensitivity213303_ActualPrefixCaps
import Definitions.Def_Sensitivity213303_ActualResidualCaps
import Definitions.Def_Sensitivity213303_ActualTargetAccounting
import Definitions.Def_Sensitivity213303_CandidateCoherence
import Definitions.Def_Sensitivity213303_CapAlgorithm
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
namespace ThreeBoundAccounting
end ThreeBoundAccounting
namespace ThreeBoundActualEnumeration
end ThreeBoundActualEnumeration
namespace ThreeBoundActualHeadCosts
end ThreeBoundActualHeadCosts
namespace ThreeBoundActualResidualCaps
end ThreeBoundActualResidualCaps
namespace ThreeBoundActualTargets
end ThreeBoundActualTargets
namespace ThreeBoundCapAlgorithm
end ThreeBoundCapAlgorithm
namespace ThreeBoundGradedCandidates
end ThreeBoundGradedCandidates
namespace ThreeBoundGradedCover
end ThreeBoundGradedCover
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
set_option maxHeartbeats 6000000
set_option maxRecDepth 10000

namespace ThreeBoundActualCaps
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundGradedCandidates
open ThreeBoundGradedCover ThreeBoundActualHeadCosts ThreeBoundActualEnumeration
open ThreeBoundActualTargets ThreeBoundActualResidualCaps ThreeBoundTagPrefixes
open ThreeBoundNumeric ThreeBoundCapAlgorithm ThreeBoundRecordCaps ThreeBoundAccounting
open scoped Classical BigOperators
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]

/-- The combinatorial exclusions used by the numerical q2 prefix routine. -/
structure CapsSound (R : V → V → Prop) (ell : V → V → Bool) (caps : Caps) : Prop where
  ordinary : ∀ q, q ≤ 2 → CandidateCoherence.NoOrdinary R ell q (Caps.at caps.ordinary q)
  source : ResidualCaps.DominatorCardBound R ell 1 (caps.pcross+1)
  double : ResidualCaps.DominatorCardBound R ell 2 (Caps.at caps.zero 2+1)
  markedOne : ∀ q, 1 ≤ q → q ≤ 2 →
    ResidualCaps.MarkedCardBound R ell q 1 (q+1) (Caps.at caps.marked (q-1))
  markedTwo : ∀ q, 1 ≤ q → q ≤ 2 →
    ResidualCaps.MarkedCardBound R ell q 2 (2*(q+1))
      (Caps.at caps.marked (if q=1 then 4 else 5))
  zeroThree : ResidualCaps.MarkedCardBound R ell 1 3 0 (Caps.at caps.marked 6)
  zeroFour : ResidualCaps.MarkedCardBound R ell 2 4 0 (Caps.at caps.marked 7)
  zeroThree_pos : 1 ≤ Caps.at caps.marked 6
  zeroFour_pos : 1 ≤ Caps.at caps.marked 7



end
end ThreeBoundActualCaps


