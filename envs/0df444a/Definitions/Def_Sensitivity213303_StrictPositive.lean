-- Prove2me | Definitions.Def_Sensitivity213303_StrictPositive
-- name    : Sensitivity213303_StrictPositive
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-25T22:21:32.570992+00:00
-- url     : https://prove2.me/theorems/4348ddac-587c-4a21-be2d-92f59c0ce1aa
-- title:
--   Outgoing strict candidates and their selected target repairs
-- statement:
--   Relative to a fixed row p, strictOutHeads consists of vertices v with p→v that are strict target candidates for the designated zero-tolerance parent. strictOutBits unions the target-upward flip sets of their children selected by the labels of p→v. These sets are the outgoing part of the strict parent-repair cover and are bounded using a one-marker coherent exclusion.
-- source:
--   Original Lean formalization for the Prove2Me block-sensitivity-versus-sensitivity campaign, module StrictPositive; source SHA256 549e6ba1808bd229a847f779827b54a74eae41146d2a38e7d8ed2b2cf1b42923.

/- Refined strict conditional positive transfer, including source-labeled cap. -/
import Definitions.Def_Sensitivity213303_CandidateCoherence
import Definitions.Def_Sensitivity213303_ConditionalOrdinary
import Definitions.Def_Sensitivity213303_GradedPositiveBoundary
import Definitions.Def_Sensitivity213303_GuardAugmentation
import Definitions.Def_Sensitivity213303_ProfileClosures
import Definitions.Def_Sensitivity213303_Q2CandidateTypes
import Definitions.Def_Sensitivity213303_Q2Enumeration
import Definitions.Def_Sensitivity213303_RecursiveLowerBounds
import Definitions.Def_Sensitivity213303_ResidualCaps
import Definitions.Def_Sensitivity213303_StrictUnion
import Definitions.Def_Sensitivity213303_TournamentHighRows
import Definitions.Def_Sensitivity213303_WitnessLifting
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.BigOperators
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
namespace ThreeBoundWitness
end ThreeBoundWitness


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false

namespace ThreeBoundConditional
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open scoped BigOperators Classical
noncomputable section

variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

def strictOutHeads (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (tl gl : L) (x : ((V × Bool) × I) → Bool) (p : V) : Finset V :=
  Finset.univ.filter fun v => S.Adj p v ∧ StrictTargetCandidate S F tl gl x v

def strictOutBits (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (tl gl : L) (x : ((V × Bool) × I) → Bool) (p : V) : Finset ((V × Bool) × I) :=
  (strictOutHeads S F tl gl x p).biUnion fun v =>
    liftBits v (S.label p v) (flipsTo (F tl) true (child x v (S.label p v)))

































end
end ThreeBoundConditional


