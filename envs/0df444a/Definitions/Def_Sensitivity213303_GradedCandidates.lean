-- Prove2me | Definitions.Def_Sensitivity213303_GradedCandidates
-- name    : Sensitivity213303_GradedCandidates
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-25T22:20:15.024421+00:00
-- url     : https://prove2.me/theorems/bf3dc7d2-d92e-4913-9ca7-7bec1988a7e3
-- title:
--   Semantic data for an ordered weak/strong graded parent pair
-- statement:
--   PairData connects two parent levels to their weak and strong target-threshold functions. It records monotonicity in failure count, the order of guard levels and tolerances, the pointwise weak-to-strong target order, and exact identities expressing each target test as the conjunction of its two child functions. It also requires the relevant guard level to lie below its target thresholds. These hypotheses justify the candidate classification and conditional head-cost estimates for actual Boolean inputs.
-- source:
--   Original Lean formalization for the Prove2Me block-sensitivity-versus-sensitivity campaign, module GradedCandidates; source SHA256 b678c8d2d17ede20517cee0be5f70571b803e9e5a8ee20483d5fef6346a7243d.

/- Actual weak rejection constraints for the q2 head-cost formulas. -/
import Definitions.Def_Sensitivity213303_CandidateCoherence
import Definitions.Def_Sensitivity213303_GradedPositiveBoundary
import Definitions.Def_Sensitivity213303_GuardAugmentation
import Definitions.Def_Sensitivity213303_HeadCosts
import Definitions.Def_Sensitivity213303_ProfileClosures
import Definitions.Def_Sensitivity213303_Q2CandidateTypes
import Definitions.Def_Sensitivity213303_Q2Enumeration
import Definitions.Def_Sensitivity213303_RecursiveLowerBounds
import Definitions.Def_Sensitivity213303_TournamentHighRows
import Definitions.Def_Sensitivity213303_WitnessLifting
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
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
namespace OAI.Paper320
end OAI.Paper320
namespace ThreeBoundPositive
end ThreeBoundPositive
namespace ThreeBoundProfiles
end ThreeBoundProfiles
namespace ThreeBoundRepair
end ThreeBoundRepair
namespace ThreeBoundWitness
end ThreeBoundWitness


set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

namespace ThreeBoundGradedCandidates
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive ThreeBoundRepair
open scoped Classical
noncomputable section
variable {L I V : Type} [Preorder L] [Fintype I] [Fintype V]

structure PairData (S : Stage L I V) (F : L → (I → Bool) → Bool) (i j : L) where
  weak : ℕ → L
  strong : ℕ → L
  weakMono : Monotone weak
  strongMono : Monotone strong
  guards : S.guard j ≤ S.guard i
  tolerances : S.tolerance j ≤ S.tolerance i
  targets : ∀ b, b ≤ S.tolerance j → weak b ≤ strong b
  weakDef : ∀ d u z, S.target i d u z = (F (weak d) u && F (weak d) z)
  strongDef : ∀ d u z, S.target j d u z = (F (strong d) u && F (strong d) z)
  guardTarget : ∀ b, b ≤ S.tolerance j → S.guard j ≤ strong b
  weakGuardTarget : ∀ b, b ≤ S.tolerance i → S.guard i ≤ weak b

variable (S : Stage L I V) (F : L → (I → Bool) → Bool) (hF : Nested F)
  (i j : L) (P : PairData S F i j) (x : ((V × Bool) × I) → Bool)
include hF P

















end
end ThreeBoundGradedCandidates


