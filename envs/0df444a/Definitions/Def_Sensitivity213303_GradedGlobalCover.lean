-- Prove2me | Definitions.Def_Sensitivity213303_GradedGlobalCover
-- name    : Sensitivity213303_GradedGlobalCover
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-25T22:21:37.27177+00:00
-- url     : https://prove2.me/theorems/39cb7a2c-945f-46e6-bdcc-507f79fdc1b3
-- title:
--   The actual three-part cover of graded parent repairs
-- statement:
--   The construction classifies actual rows into target candidates, guard sources, high heads and negative targets. Each target candidate has a designated missing child. Incoming guard sources select a finite set of hit children at each high head. actualHeadParts unions the relevant target repair with repairs at those hit children. The complete geometric cover consists of highBits, negativeBits and externalBits, corresponding respectively to high heads, non-high target candidates and failed-guard heads outside the high set.
-- source:
--   Original Lean formalization for the Prove2Me block-sensitivity-versus-sensitivity campaign, module GradedGlobalCover; source SHA256 bb5bcba294b60d2080cea6152e5a8ed3e393101f50bb6829c5883a2fa0c78f46.

/- Actual upward flips grouped into negative targets, high heads and external
   failed-guard arcs. Internal arcs are deduplicated by their selected child. -/
import Definitions.Def_Sensitivity213303_CandidateCoherence
import Definitions.Def_Sensitivity213303_GradedCandidates
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
namespace ThreeBoundHeadCharge
end ThreeBoundHeadCharge
namespace ThreeBoundPositive
end ThreeBoundPositive
namespace ThreeBoundProfiles
end ThreeBoundProfiles
namespace ThreeBoundWitness
end ThreeBoundWitness


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

namespace ThreeBoundGradedCover
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive ThreeBoundHeadCharge
open scoped Classical BigOperators
noncomputable section
variable {L I V : Type} [Preorder L] [Fintype I] [Fintype V]

def targetAt (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t : ℕ → L) (l : L) (x : ((V × Bool) × I) → Bool) (v : V) : Prop :=
  Q2CandidateTypes.TargetCandidate (fun b z => F (t b) z = true)
    (S.tolerance l) (failed S F l x v).card (failed S F l x v).card
      (child x v false) (child x v true)

def guardAt (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t : ℕ → L) (l : L) (x : ((V × Bool) × I) → Bool) (v : V) : Prop :=
  ∃ b, Q2CandidateTypes.GuardCandidate (fun k z => F (t k) z = true)
    (S.tolerance l) (failed S F l x v).card b (child x v false) (child x v true)

def highAt (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t : ℕ → L) (l : L) (x : ((V × Bool) × I) → Bool) (v : V) : Prop :=
  Q2CandidateTypes.High (fun z => F (S.guard l) z = true)
    (fun b z => F (t b) z = true) (S.tolerance l) (failed S F l x v).card
      (child x v false) (child x v true)

def highHeads (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t : ℕ → L) (l : L) (x : ((V × Bool) × I) → Bool) : Finset V :=
  Finset.univ.filter (highAt S F t l x)

def guardSources (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t : ℕ → L) (l : L) (x : ((V × Bool) × I) → Bool) : Finset V :=
  Finset.univ.filter (guardAt S F t l x)

def negativeTargets (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t : ℕ → L) (l : L) (x : ((V × Bool) × I) → Bool) : Finset V :=
  Finset.univ.filter fun v => targetAt S F t l x v ∧ ¬ highAt S F t l x v

def missing (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t : ℕ → L) (l : L) (x : ((V × Bool) × I) → Bool) (v : V) : Bool :=
  if F (t (failed S F l x v).card) (child x v false) = true then true else false

def incomingSources (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t : ℕ → L) (l : L) (x : ((V × Bool) × I) → Bool) (w : V) : Finset V :=
  (guardSources S F t l x).filter fun v => S.Adj v w

def hitChildren (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t : ℕ → L) (l : L) (x : ((V × Bool) × I) → Bool) (w : V) : Finset Bool :=
  (incomingSources S F t l x w).image fun v => S.label v w



def actualHeadParts (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t : ℕ → L) (l : L) (x : ((V × Bool) × I) → Bool) (w : V) (c : Bool) : Finset I :=
  (if targetAt S F t l x w ∧ c = missing S F t l x w then
    flipsTo (F (t (failed S F l x w).card)) true (child x w c) else ∅) ∪
  (if c ∈ hitChildren S F t l x w then flipsTo (F (S.guard l)) false (child x w c) else ∅)

def highBits (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t : ℕ → L) (l : L) (x : ((V × Bool) × I) → Bool) : Finset ((V × Bool) × I) :=
  (highHeads S F t l x).biUnion fun w => headBits w (actualHeadParts S F t l x w)

def negativeBits (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t : ℕ → L) (l : L) (x : ((V × Bool) × I) → Bool) : Finset ((V × Bool) × I) :=
  (negativeTargets S F t l x).biUnion fun w => liftBits w (missing S F t l x w)
    (flipsTo (F (t (failed S F l x w).card)) true (child x w (missing S F t l x w)))

def externalBits (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t : ℕ → L) (l : L) (x : ((V × Bool) × I) → Bool) : Finset ((V × Bool) × I) :=
  (guardSources S F t l x).biUnion fun v =>
    (failed S F l x v \ highHeads S F t l x).biUnion fun w =>
      liftBits w (S.label v w)
        (flipsTo (F (S.guard l)) false (child x w (S.label v w)))







end
end ThreeBoundGradedCover


