-- Prove2me | Definitions.Def_Sensitivity213981Formal_ConditionalOrdinary
-- name    : Sensitivity213981Formal_ConditionalOrdinary
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T19:30:17.954394+00:00
-- url     : https://prove2.me/theorems/aca24052-32d9-433d-b6d4-27dd6cb95176
-- title:
--   Conditional Ordinary — sensitivity certificate definitions
-- statement:
--   The definitions for Conditional Ordinary in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundConditional.guardFailures`, `ThreeBoundConditional.ordinaryRow`, `ThreeBoundConditional.ordinaryRowBool`, `ThreeBoundConditional.ordinaryStage`, `ThreeBoundConditional.passingGuards`, `ThreeBoundConditional.ordinaryGuardBits`, `ThreeBoundConditional.ordinaryParent`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; ConditionalOrdinary.lean, lines 1–714.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Supplement_GradedPositiveBoundary
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Sensitivity213981Formal
section
/-
Ordinary-component conditional transfers for the actual guarded Boolean family.
This development uses the shared campaign bit-flip definitions throughout.
-/


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
  (∀ c : Bool, F t (child x v c) = true) ∧ (guardFailures S F g x v).card ≤  q


















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




end
end Sensitivity213981Formal


