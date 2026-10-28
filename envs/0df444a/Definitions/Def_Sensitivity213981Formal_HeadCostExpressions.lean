-- Prove2me | Definitions.Def_Sensitivity213981Formal_HeadCostExpressions
-- name    : Sensitivity213981Formal_HeadCostExpressions
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T19:54:24.565007+00:00
-- url     : https://prove2.me/theorems/d5c34590-f833-44e2-b7b1-e36fe0d2d77b
-- title:
--   Head Cost Expressions — sensitivity certificate definitions
-- statement:
--   The definitions for Head Cost Expressions in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundHeadExpressions.EntryMatch`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; HeadCostExpressions.lean, lines 1–228.

import Definitions.Def_Sensitivity213981Formal_GradedCandidates
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Q2RawExpressions
import Definitions.Def_Sensitivity213981Formal_Supplement_NumericExpressions
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Nat
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
import Mathlib.Tactic.Ring

namespace Sensitivity213981Formal
section
/- Interpreting the exact numeric q2 head-cost expressions on actual heads. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

namespace ThreeBoundHeadExpressions
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundHeadCharge ThreeBoundGradedCandidates ThreeBoundGradedCover ThreeBoundActualHeadCosts
open ThreeBoundNumeric ThreeBoundFullProfile
open scoped Classical
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]













structure EntryMatch (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool)
    (i j : Fin n) (P : PairData S F i j) (a c : Entry) : Prop where
  weakGuard : (S.guard i).val = a.guard
  strongGuard : (S.guard j).val = c.guard
  weakTolerance : S.tolerance i = a.tolerance
  strongTolerance : S.tolerance j = c.tolerance
  weakThreshold : ∀ b, (P.weak b).val = a.threshold b
  strongThreshold : ∀ b, (P.strong b).val = c.threshold b











end
end ThreeBoundHeadExpressions






end
end Sensitivity213981Formal


