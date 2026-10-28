-- Prove2me | Definitions.Def_Sensitivity213981Formal_HeadCosts
-- name    : Sensitivity213981Formal_HeadCosts
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T19:43:08.830276+00:00
-- url     : https://prove2.me/theorems/c2e88866-dba4-45da-b1ec-b50498c6121a
-- title:
--   Head Costs — sensitivity certificate definitions
-- statement:
--   The definitions for Head Costs in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundHeadCharge.headBits`, `ThreeBoundHeadCharge.guardParts`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; HeadCosts.lean, lines 1–244.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Supplement_GradedPositiveBoundary
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Sensitivity213981Formal
section
/- Actual conditional boundary costs at one two-child head. -/


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























def guardParts (F : L → (I → Bool) → Bool) (g : L)
    (x : Bool → I → Bool) (hit : Finset Bool) (c : Bool) : Finset I :=
  if c ∈ hit then flipsTo (F g) false (x c) else ∅









end
end ThreeBoundHeadCharge





end
end Sensitivity213981Formal


