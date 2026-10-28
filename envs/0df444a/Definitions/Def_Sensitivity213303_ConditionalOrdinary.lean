-- Prove2me | Definitions.Def_Sensitivity213303_ConditionalOrdinary
-- name    : Sensitivity213303_ConditionalOrdinary
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-25T21:59:49.042532+00:00
-- url     : https://prove2.me/theorems/11161688-100a-4077-bc8e-4544ff7af3ae
-- title:
--   Ordinary rows and parents for conditional profile transfers
-- statement:
--   An ordinary row at target t, guard g and tolerance q requires both target children to accept and at most q outgoing selected guard children to accept. ordinaryRowBool turns this condition into a Boolean function, and ordinaryParent takes the disjunction over all rows. The accompanying guard-failure, passing-guard and repair-bit sets describe how a single input flip can destroy a fixed winning row. These definitions are shared by the conditional M, P and D transfer proofs.
-- source:
--   Original Lean formalization for the Prove2Me block-sensitivity-versus-sensitivity campaign, module ConditionalOrdinary; source SHA256 f3399d34ca31ad9b4ad9de5a4ab294181bbd230bb91c7ec217c0414e4e592080.

/-
Ordinary-component conditional transfers for the actual guarded Boolean family.
This development uses the shared campaign bit-flip definitions throughout.
-/
import Definitions.Def_Sensitivity213303_GradedPositiveBoundary
import Definitions.Def_Sensitivity213303_ProfileClosures
import Definitions.Def_Sensitivity213303_RecursiveLowerBounds
import Definitions.Def_Sensitivity213303_WitnessLifting
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
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
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

namespace ThreeBoundConditional
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open scoped BigOperators Classical
noncomputable section

variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

def ordinaryStage (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t g : L) (q : ℕ) : Stage L I V where
  Adj := S.Adj
  loopless := S.loopless
  label := S.label
  guard := fun _ => g
  tolerance := fun _ => q
  target := fun _ _ u z => F t u && F t z

def ordinaryParent (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t g : L) (q : ℕ) := parent (ordinaryStage S F t g q) F t

def guardFailures (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (g : L) (x : ((V × Bool) × I) → Bool) (v : V) : Finset V :=
  Finset.univ.filter fun w => S.Adj v w ∧ F g (child x w (S.label v w)) = true

def ordinaryRow (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t g : L) (q : ℕ) (x : ((V × Bool) × I) → Bool) (v : V) : Prop :=
  (∀ c : Bool, F t (child x v c) = true) ∧ (guardFailures S F g x v).card ≤ q


















def passingGuards (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (g : L) (x : ((V × Bool) × I) → Bool) (v : V) : Finset V :=
  outgoing S v \ guardFailures S F g x v





def ordinaryGuardBits (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (gi gj : L) (x : ((V × Bool) × I) → Bool) (v : V) : Finset ((V × Bool) × I) :=
  (passingGuards S F gj x v).biUnion fun w =>
    liftBits w (S.label v w) (flipsTo (F gi) true (child x w (S.label v w)))





















def ordinaryRowBool (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t g : L) (q : ℕ) (v : V) (x : ((V × Bool) × I) → Bool) : Bool :=
  decide (ordinaryRow S F t g q x v)




















end
end ThreeBoundConditional


