-- Prove2me | Definitions.Def_Sensitivity213303_CapAlgorithm
-- name    : Sensitivity213303_CapAlgorithm
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-25T22:22:19.33166+00:00
-- url     : https://prove2.me/theorems/20f5a829-e844-408b-badc-301a2b89cdb4
-- title:
--   Record-based counts used by the target-prefix cap algorithm
-- statement:
--   For an exact q≤2 record, lowCount(q) sums the counts of kinds outside the positive prefix whose budget is at most q; nextCount(q) uses budget at most q+1. eligibleCount(q) sums all kind counts with budget at most q+1. These purely numerical quantities match the actual outside-high and eligible-high counts, allowing the prefix-cap algorithm to combine ordinary, source, dominator and marked exclusions.
-- source:
--   Original Lean formalization for the Prove2Me block-sensitivity-versus-sensitivity campaign, module CapAlgorithm; source SHA256 f6ba20d1d9b36b58f2afc8f1b744cbedfa0c71a2875d9ab5af50a7161880f316.

/- Numerical prefix-cap composition, separated from its actual candidate
proofs. Each premise is one of the independently established labeling caps. -/
import Definitions.Def_Sensitivity213303_CandidateCoherence
import Definitions.Def_Sensitivity213303_FullProfileClosure
import Definitions.Def_Sensitivity213303_GlobalAccounting
import Definitions.Def_Sensitivity213303_GradedPositiveBoundary
import Definitions.Def_Sensitivity213303_GuardAugmentation
import Definitions.Def_Sensitivity213303_NumericExpressions
import Definitions.Def_Sensitivity213303_ProfileClosures
import Definitions.Def_Sensitivity213303_Q2CandidateTypes
import Definitions.Def_Sensitivity213303_Q2Enumeration
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
namespace ThreeBoundNumeric
end ThreeBoundNumeric


set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 10000

namespace ThreeBoundCapAlgorithm
open ThreeBoundNumeric
open scoped BigOperators Classical

def lowCount (x : Q2Record) (q : ℕ) : ℕ :=
  ((List.range 8).filterMap fun t =>
    if !positiveInside t q ∧ kindBudget t ≤ q then some (x t) else none).sum

def nextCount (x : Q2Record) (q : ℕ) : ℕ :=
  ((List.range 8).filterMap fun t =>
    if !positiveInside t q ∧ kindBudget t ≤ q+1 then some (x t) else none).sum

def eligibleCount (x : Q2Record) (q : ℕ) : ℕ :=
  ((List.range 8).filterMap fun t => if kindBudget t ≤ q+1 then some (x t) else none).sum





end ThreeBoundCapAlgorithm


