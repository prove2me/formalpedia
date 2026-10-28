-- Prove2me | Definitions.Def_Sensitivity213303_StrictUnion
-- name    : Sensitivity213303_StrictUnion
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-25T22:20:41.002628+00:00
-- url     : https://prove2.me/theorems/e8207654-57c4-42f2-a30d-76ae66431076
-- title:
--   The two one-flip candidate forms at zero tolerance
-- statement:
--   A StrictTargetCandidate has one false target child, its other target child true, and no failed guards. A StrictGuardCandidate has both target children true and exactly one failed guard. These are the two possible ways a false zero-tolerance ordinary row can be repaired by a single input flip, and they determine the two conditional union-bound cases.
-- source:
--   Original Lean formalization for the Prove2Me block-sensitivity-versus-sensitivity campaign, module StrictUnion; source SHA256 b8cb65cdc129887eb3729182f514b30c59d50d82acb433874b9fc2b49ed81538.

/- Strict conditional union transfer for actual Boolean rows and parents. -/
import Definitions.Def_Sensitivity213303_ConditionalOrdinary
import Definitions.Def_Sensitivity213303_GradedPositiveBoundary
import Definitions.Def_Sensitivity213303_ProfileClosures
import Definitions.Def_Sensitivity213303_RecursiveLowerBounds
import Definitions.Def_Sensitivity213303_TournamentHighRows
import Definitions.Def_Sensitivity213303_WitnessLifting
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
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











def StrictTargetCandidate (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t g : L) (x : ((V × Bool) × I) → Bool) (v : V) : Prop :=
  ∃ c : Bool, F t (child x v c)=false ∧
    (∀ e : Bool, e ≠ c → F t (child x v e)=true) ∧ guardFailures S F g x v=∅

def StrictGuardCandidate (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t g : L) (x : ((V × Bool) × I) → Bool) (v : V) : Prop :=
  (∀ e : Bool, F t (child x v e)=true) ∧ ∃ w, guardFailures S F g x v={w}























end
end ThreeBoundConditional


