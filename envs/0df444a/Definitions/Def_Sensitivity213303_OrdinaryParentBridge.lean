-- Prove2me | Definitions.Def_Sensitivity213303_OrdinaryParentBridge
-- name    : Sensitivity213303_OrdinaryParentBridge
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-25T22:37:18.317646+00:00
-- url     : https://prove2.me/theorems/66589053-aa97-43eb-bddb-dd5ef81944ce
-- title:
--   The coordinate equivalence between Fin 2 and Boolean child conventions
-- statement:
--   ordinaryCoordEquiv maps a parent coordinate ((v,c),i), where c belongs to Fin 2, to the same vertex and child coordinate with c transported through Fin 2≃Bool. The resulting equivalence preserves individual coordinate flips. It is used to identify the archived ordinary parent with the ordinaryParent interface of the new graded and min/max construction.
-- source:
--   Original Lean formalization for the Prove2Me block-sensitivity-versus-sensitivity campaign, module OrdinaryParentBridge; source SHA256 0ff90a6595c898c3e1b50e3d8e33a431225db74a8316121663c0345dca8d093d.

/- Exact coordinate and predicate bridge from the accepted ordinary proofs to
   the actual Bool-child family used by the current certificate. -/
import Definitions.Def_Sensitivity213303_ArchivedOrdinaryDefinitions
import Definitions.Def_Sensitivity213303_CandidateCoherence
import Definitions.Def_Sensitivity213303_ConditionalOrdinary
import Definitions.Def_Sensitivity213303_Endpoint40Recipes
import Definitions.Def_Sensitivity213303_GradedPositiveBoundary
import Definitions.Def_Sensitivity213303_GuardAugmentation
import Definitions.Def_Sensitivity213303_LabelCard
import Definitions.Def_Sensitivity213303_LabelDefinitions
import Definitions.Def_Sensitivity213303_LabelExists
import Definitions.Def_Sensitivity213303_LabelLoads
import Definitions.Def_Sensitivity213303_LabelMarked
import Definitions.Def_Sensitivity213303_LabelOrdinary
import Definitions.Def_Sensitivity213303_MinMaxNesting
import Definitions.Def_Sensitivity213303_Paley10007
import Definitions.Def_Sensitivity213303_ProfileClosures
import Definitions.Def_Sensitivity213303_Q2CandidateTypes
import Definitions.Def_Sensitivity213303_Q2Enumeration
import Definitions.Def_Sensitivity213303_RecursiveLowerBounds
import Definitions.Def_Sensitivity213303_ResidualCaps
import Definitions.Def_Sensitivity213303_Selected10007
import Definitions.Def_Sensitivity213303_SelectedBoolCaps
import Definitions.Def_Sensitivity213303_SelectedOrdinaryCaps
import Definitions.Def_Sensitivity213303_StrictPositive
import Definitions.Def_Sensitivity213303_StrictUnion
import Definitions.Def_Sensitivity213303_TournamentHighRows
import Definitions.Def_Sensitivity213303_WitnessLifting
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
namespace OAI.Paper320
end OAI.Paper320
namespace ThreeBoundPositive
end ThreeBoundPositive
namespace ThreeBoundProfiles
end ThreeBoundProfiles
namespace ThreeBoundWitness
end ThreeBoundWitness


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false

namespace ThreeBoundConditional
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open scoped Classical
noncomputable section

variable {I J : Type} [Fintype I] [Fintype J]



variable {n k : ℕ}

def ordinaryCoordEquiv : ((Fin k × Fin 2) × I) ≃ ((Fin k × Bool) × I) :=
  Equiv.prodCongr (Equiv.prodCongr (Equiv.refl _) finTwoEquiv) (Equiv.refl _)
















end
end ThreeBoundConditional


