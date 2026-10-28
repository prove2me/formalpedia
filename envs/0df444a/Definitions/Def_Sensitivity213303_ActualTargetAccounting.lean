-- Prove2me | Definitions.Def_Sensitivity213303_ActualTargetAccounting
-- name    : Sensitivity213303_ActualTargetAccounting
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-25T22:23:26.6431+00:00
-- url     : https://prove2.me/theorems/c47f7b9a-3ff0-4d68-986e-2483b4c75cfb
-- title:
--   Actual target prefixes and negative-target tiers
-- statement:
--   targetPrefix(q) is the set of actual target candidates with at most q failed guards. negativeTier(b) is the set of actual negative targets with exactly b failed guards. Prefix caps bound how many targets can occur up to each level; grouping negative repair costs by these exact tiers then produces a weighted sum of child A bounds.
-- source:
--   Original Lean formalization for the Prove2Me block-sensitivity-versus-sensitivity campaign, module ActualTargetAccounting; source SHA256 ad133c8c9a1c6d76f1d1211b907c87689cb8d2b17dd457c45348e335ce3f0ebe.

/- Actual target candidate prefixes and their negative repair contribution. -/
import Definitions.Def_Sensitivity213303_ActualPrefixCaps
import Definitions.Def_Sensitivity213303_CandidateCoherence
import Definitions.Def_Sensitivity213303_GlobalAccounting
import Definitions.Def_Sensitivity213303_GradedCandidates
import Definitions.Def_Sensitivity213303_GradedGlobalCover
import Definitions.Def_Sensitivity213303_GradedPositiveBoundary
import Definitions.Def_Sensitivity213303_GuardAugmentation
import Definitions.Def_Sensitivity213303_HeadCosts
import Definitions.Def_Sensitivity213303_ProfileClosures
import Definitions.Def_Sensitivity213303_Q2CandidateTypes
import Definitions.Def_Sensitivity213303_Q2Enumeration
import Definitions.Def_Sensitivity213303_Q2EnumerationBridge
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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
namespace OAI.Paper320
end OAI.Paper320
namespace ThreeBoundActualEnumeration
end ThreeBoundActualEnumeration
namespace ThreeBoundActualHeadCosts
end ThreeBoundActualHeadCosts
namespace ThreeBoundGradedCandidates
end ThreeBoundGradedCandidates
namespace ThreeBoundGradedCover
end ThreeBoundGradedCover
namespace ThreeBoundPositive
end ThreeBoundPositive
namespace ThreeBoundPrefixCaps
end ThreeBoundPrefixCaps
namespace ThreeBoundProfiles
end ThreeBoundProfiles
namespace ThreeBoundWitness
end ThreeBoundWitness


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false

namespace ThreeBoundActualTargets
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundGradedCandidates ThreeBoundGradedCover ThreeBoundActualHeadCosts
open ThreeBoundActualEnumeration ThreeBoundPrefixCaps
open scoped Classical BigOperators
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

def targetPrefix (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool) (q : ℕ) : Finset V :=
  Finset.univ.filter fun v => targetAt S F t j x v ∧ (failed S F j x v).card ≤ q

def negativeTier (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t : ℕ → L) (j : L) (x : ((V × Bool) × I) → Bool) (b : ℕ) : Finset V :=
  (negativeTargets S F t j x).filter fun v => (failed S F j x v).card = b

















end
end ThreeBoundActualTargets


