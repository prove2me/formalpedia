-- Prove2me | Definitions.Def_Sensitivity213981Formal_GradedCandidates
-- name    : Sensitivity213981Formal_GradedCandidates
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T19:44:54.831163+00:00
-- url     : https://prove2.me/theorems/30e661fd-866b-4f9e-bb08-3c3a02f2e5e2
-- title:
--   Graded Candidates — sensitivity certificate definitions
-- statement:
--   The definitions for Graded Candidates in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundGradedCandidates.PairData`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; GradedCandidates.lean, lines 1–146.

import Definitions.Def_Sensitivity213981Formal_GuardAugmentation
import Definitions.Def_Sensitivity213981Formal_HeadCosts
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Supplement_GradedPositiveBoundary
import Definitions.Def_Sensitivity213981Formal_Supplement_Q2Enumeration
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Sensitivity213981Formal
section
/- Actual weak rejection constraints for the q2 head-cost formulas. -/


set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

namespace ThreeBoundGradedCandidates
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive ThreeBoundRepair
open scoped Classical
noncomputable section
variable {L I V : Type} [Preorder L] [Fintype I] [Fintype V]

structure PairData (S : Stage L I V) (F : L → (I → Bool) → Bool) (i j : L) where
  weak : ℕ → L
  strong : ℕ → L
  weakMono : Monotone weak
  strongMono : Monotone strong
  guards : S.guard j ≤  S.guard i
  tolerances : S.tolerance j ≤  S.tolerance i
  targets : ∀ b, b ≤  S.tolerance j → weak b ≤  strong b
  weakDef : ∀ d u z, S.target i d u z = (F (weak d) u && F (weak d) z)
  strongDef : ∀ d u z, S.target j d u z = (F (strong d) u && F (strong d) z)
  guardTarget : ∀ b, b ≤  S.tolerance j → S.guard j ≤  strong b
  weakGuardTarget : ∀ b, b ≤  S.tolerance i → S.guard i ≤  weak b

variable (S : Stage L I V) (F : L → (I → Bool) → Bool) (hF : Nested F)
  (i j : L) (P : PairData S F i j) (x : ((V × Bool) × I) → Bool)
include hF P

















end
end ThreeBoundGradedCandidates






end
end Sensitivity213981Formal


