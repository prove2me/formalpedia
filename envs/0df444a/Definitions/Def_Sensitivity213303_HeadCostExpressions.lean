-- Prove2me | Definitions.Def_Sensitivity213303_HeadCostExpressions
-- name    : Sensitivity213303_HeadCostExpressions
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-25T22:22:32.670984+00:00
-- url     : https://prove2.me/theorems/a77bda00-e8fc-450a-a7cb-fd65299db629
-- title:
--   Exact matching between recipe entries and semantic parent levels
-- statement:
--   EntryMatch records that the natural-number fields of a weak and strong recipe entry agree with the corresponding finite levels in PairData: both guard levels, both tolerances, and every weak and strong target threshold. This equality certificate lets each symbolic head-cost formula be interpreted at the exact levels used by the actual Boolean construction.
-- source:
--   Original Lean formalization for the Prove2Me block-sensitivity-versus-sensitivity campaign, module HeadCostExpressions; source SHA256 86dcbb11c5c1af194bcda98ae1161b497e554b8052573bd522fa628f8ee5d7b0.

/- Interpreting the exact numeric q2 head-cost expressions on actual heads. -/
import Definitions.Def_Sensitivity213303_CandidateCoherence
import Definitions.Def_Sensitivity213303_FullProfileClosure
import Definitions.Def_Sensitivity213303_GradedCandidates
import Definitions.Def_Sensitivity213303_GradedGlobalCover
import Definitions.Def_Sensitivity213303_GradedPositiveBoundary
import Definitions.Def_Sensitivity213303_GuardAugmentation
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
namespace ThreeBoundFullProfile
end ThreeBoundFullProfile
namespace ThreeBoundGradedCandidates
end ThreeBoundGradedCandidates
namespace ThreeBoundGradedCover
end ThreeBoundGradedCover
namespace ThreeBoundHeadCharge
end ThreeBoundHeadCharge
namespace ThreeBoundNumeric
end ThreeBoundNumeric
namespace ThreeBoundPositive
end ThreeBoundPositive
namespace ThreeBoundProfiles
end ThreeBoundProfiles
namespace ThreeBoundWitness
end ThreeBoundWitness


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

namespace ThreeBoundHeadExpressions
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundHeadCharge ThreeBoundGradedCandidates ThreeBoundGradedCover ThreeBoundActualHeadCosts
open ThreeBoundNumeric ThreeBoundFullProfile
open scoped Classical
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]













structure EntryMatch (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool)
    (i j : Fin n) (P : PairData S F i j) (a c : Entry) : Prop where
  weakGuard : (S.guard i).val = a.guard
  strongGuard : (S.guard j).val = c.guard
  weakTolerance : S.tolerance i = a.tolerance
  strongTolerance : S.tolerance j = c.tolerance
  weakThreshold : ∀ b, (P.weak b).val = a.threshold b
  strongThreshold : ∀ b, (P.strong b).val = c.threshold b











end
end ThreeBoundHeadExpressions


