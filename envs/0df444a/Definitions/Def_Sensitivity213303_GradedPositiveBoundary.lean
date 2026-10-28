-- Prove2me | Definitions.Def_Sensitivity213303_GradedPositiveBoundary
-- name    : Sensitivity213303_GradedPositiveBoundary
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-25T21:57:15.40279+00:00
-- url     : https://prove2.me/theorems/e36695d9-b1e5-4606-befd-87492175ebd9
-- title:
--   Target and guard bit sets that can destroy a winning graded row
-- statement:
--   For a winning row, targetBits is the union of the downward-sensitivity sets of its two target children, lifted into their parent input blocks. The passing guards are its outgoing neighbors outside the actual failed-guard set. guardBits collects upward flips that can activate one of these passing guards at the weak guard level. ExtraFailure describes precisely such a newly activated selected child. These sets provide the geometric cover used to bound downward sensitivity of a graded parent.
-- source:
--   Original Lean formalization for the Prove2Me block-sensitivity-versus-sensitivity campaign, module GradedPositiveBoundary; source SHA256 6d85f6c7ba65c7b083899b73aafdf9256265e82b0d8bcdb147fb371d8519a028.

/-
Actual positive-boundary transfer for equal-target graded rows.
Every guard count and bit flip below uses the concrete guarded construction.
This is one part of the upper transfer, not a complete seed proof.
-/
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
namespace ThreeBoundProfiles
end ThreeBoundProfiles
namespace ThreeBoundWitness
end ThreeBoundWitness


set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option linter.unusedSectionVars false

namespace ThreeBoundPositive
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles
open scoped BigOperators Classical
noncomputable section

variable {L I V : Type} [Preorder L] [Fintype I] [Fintype V]

def ExtraFailure (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (i j : L) (x : ((V × Bool) × I) → Bool) (v w : V) (c : Bool) (a : I) : Prop :=
  S.Adj v w ∧ S.label v w = c ∧
    F (S.guard j) (child x w c) = false ∧
    F (S.guard i) (flip (child x w c) {a}) = true













def childEmbedding (v : V) (c : Bool) : I ↪ ((V × Bool) × I) :=
  ⟨fun a => ((v,c),a), fun _ _ h => congrArg Prod.snd h⟩

def liftBits (v : V) (c : Bool) (s : Finset I) : Finset ((V × Bool) × I) :=
  s.map (childEmbedding v c)





def outgoing (S : Stage L I V) (v : V) : Finset V :=
  Finset.univ.filter (S.Adj v)

def passing (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (j : L) (x : ((V × Bool) × I) → Bool) (v : V) : Finset V :=
  outgoing S v \ failed S F j x v





def targetBits (F : L → (I → Bool) → Bool) (t : L)
    (x : ((V × Bool) × I) → Bool) (v : V) : Finset ((V × Bool) × I) :=
  liftBits v false (flipsTo (F t) false (child x v false)) ∪
    liftBits v true (flipsTo (F t) false (child x v true))

def guardBits (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (i j : L) (x : ((V × Bool) × I) → Bool) (v : V) : Finset ((V × Bool) × I) :=
  (passing S F j x v).biUnion fun w =>
    liftBits w (S.label v w) (flipsTo (F (S.guard i)) true (child x w (S.label v w)))













end
end ThreeBoundPositive


