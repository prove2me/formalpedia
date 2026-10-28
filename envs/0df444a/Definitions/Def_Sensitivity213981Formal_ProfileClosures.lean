-- Prove2me | Definitions.Def_Sensitivity213981Formal_ProfileClosures
-- name    : Sensitivity213981Formal_ProfileClosures
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T17:08:46.128437+00:00
-- url     : https://prove2.me/theorems/467dc546-3fea-485a-b4d6-7d598a6a7dad
-- title:
--   Profile Closures — sensitivity certificate definitions
-- statement:
--   The definitions for Profile Closures in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundProfiles.MBound`, `ThreeBoundProfiles.PBound`, `ThreeBoundProfiles.DBound`, `ThreeBoundProfiles.Nested`, `ThreeBoundProfiles.flipsTo`, `ThreeBoundProfiles.ABound`, `ThreeBoundProfiles.BBound`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; ProfileClosures.lean, lines 1–195.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset

namespace Sensitivity213981Formal
section
/-
Dimension-independent semantics and closure rules for the five sensitivity
profiles. These prove the local soundness of the closure operations, not the
raw graded/min-max transfer formulas or their finite case-table coverage.
-/


set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ThreeBoundProfiles
open OAI.Paper320
noncomputable section
open scoped Classical

variable {L I : Type} [Preorder L] [Fintype I]

def Nested (F : L → (I → Bool) → Bool) : Prop :=
  ∀ i j, i ≤ j → ∀ x, F j x = true → F i x = true

noncomputable def flipsTo (f : (I → Bool) → Bool) (b : Bool) (x : I → Bool) : Finset I := by
  classical
  exact Finset.univ.filter fun a => f (flip x {a}) = b

def ABound (F : L → (I → Bool) → Bool) (i j : L) (v : ℕ) : Prop :=
  ∀ x, F i x = false → (flipsTo (F j) true x).card ≤ v

def BBound (F : L → (I → Bool) → Bool) (i j : L) (v : ℕ) : Prop :=
  ∀ x, F j x = true → (flipsTo (F i) false x).card ≤ v

def MBound (F : L → (I → Bool) → Bool) (i j k : L) (v : ℕ) : Prop :=
  ∀ x, F j x = true → F k x = false → (flipsTo (F i) false x).card ≤ v

def PBound (F : L → (I → Bool) → Bool) (i j k : L) (v : ℕ) : Prop :=
  ∀ x, F i x = true → F j x = false → (flipsTo (F k) true x).card ≤ v

def DBound (F : L → (I → Bool) → Bool) (i j k l : L) (v : ℕ) : Prop :=
  ∀ x, F j x = true → F k x = false →
    ((flipsTo (F i) false x) ∪ (flipsTo (F l) true x)).card ≤ v



















































end
end ThreeBoundProfiles






end
end Sensitivity213981Formal


