-- Prove2me | Definitions.Def_Sensitivity213303_HeadCosts
-- name    : Sensitivity213303_HeadCosts
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-25T22:00:45.537592+00:00
-- url     : https://prove2.me/theorems/be679ad3-06ac-4115-8b41-7c5c018b1f12
-- title:
--   Local two-child repair unions and their hit-count cost formulas
-- statement:
--   At one head, positiveParts combines repairs of a missing target child with downward repairs of whichever children are hit by incoming guard arcs; guardParts contains only the latter. headBits lifts these child sets into the parent input. Costs distinguish zero, one and at least two hits: guardCost(one,two,r) is 0, one, two; positiveCost(a,u,j,r) is a,max(u,a+j),j+max(u,a); overlapCost is a,max(u,a+j),u+j. Here a bounds the target repair, u a conditional union, and j a guard-child repair. These formulas charge overlapping repairs by their union.
-- source:
--   Original Lean formalization for the Prove2Me block-sensitivity-versus-sensitivity campaign, module HeadCosts; source SHA256 5d4a0873736723d0ebe3955104bb13e558443ffd4e86df00cd8e4f3c06d25794.

/- Actual conditional boundary costs at one two-child head. -/
import Definitions.Def_Sensitivity213303_GradedPositiveBoundary
import Definitions.Def_Sensitivity213303_ProfileClosures
import Definitions.Def_Sensitivity213303_RecursiveLowerBounds
import Definitions.Def_Sensitivity213303_WitnessLifting
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
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
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

namespace ThreeBoundHeadCharge
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open scoped Classical BigOperators
noncomputable section

variable {L I V : Type} [Preorder L] [Fintype I] [Fintype V]

def headBits (v : V) (s : Bool → Finset I) : Finset ((V × Bool) × I) :=
  liftBits v false (s false) ∪ liftBits v true (s true)







def positiveParts (F : L → (I → Bool) → Bool) (g t : L)
    (x : Bool → I → Bool) (missing : Bool) (hit : Finset Bool) (c : Bool) : Finset I :=
  (if c = missing then flipsTo (F t) true (x c) else ∅) ∪
    (if c ∈ hit then flipsTo (F g) false (x c) else ∅)

def positiveCost (a u j n : ℕ) : ℕ :=
  if n = 0 then a else if n = 1 then max u (a+j) else j + max u a









def overlapCost (a u j n : ℕ) : ℕ :=
  if n = 0 then a else if n = 1 then max u (a+j) else u+j



def guardParts (F : L → (I → Bool) → Bool) (g : L)
    (x : Bool → I → Bool) (hit : Finset Bool) (c : Bool) : Finset I :=
  if c ∈ hit then flipsTo (F g) false (x c) else ∅

def guardCost (one two n : ℕ) : ℕ :=
  if n = 0 then 0 else if n = 1 then one else two







end
end ThreeBoundHeadCharge


