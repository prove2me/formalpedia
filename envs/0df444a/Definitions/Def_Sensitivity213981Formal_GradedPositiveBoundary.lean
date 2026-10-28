-- Prove2me | Definitions.Def_Sensitivity213981Formal_GradedPositiveBoundary
-- name    : Sensitivity213981Formal_GradedPositiveBoundary
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T17:11:05.90006+00:00
-- url     : https://prove2.me/theorems/eecedcd7-49d1-4b94-88af-a8456c721f2a
-- title:
--   Graded Positive Boundary — sensitivity certificate definitions
-- statement:
--   The definitions for Graded Positive Boundary in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundPositive.ExtraFailure`, `ThreeBoundPositive.childEmbedding`, `ThreeBoundPositive.liftBits`, `ThreeBoundPositive.outgoing`, `ThreeBoundPositive.passing`, `ThreeBoundPositive.targetBits`, `ThreeBoundPositive.guardBits`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; GradedPositiveBoundary.lean, lines 1–377.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_ProfileClosures
import Definitions.Def_Sensitivity213981Formal_RecursiveLowerBounds
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
Actual positive-boundary transfer for equal-target graded rows.
Every guard count and bit flip below uses the concrete guarded construction.
This is one part of the upper transfer, not a complete seed proof.
-/


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






end
end Sensitivity213981Formal


