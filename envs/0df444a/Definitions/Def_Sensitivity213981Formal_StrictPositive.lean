-- Prove2me | Definitions.Def_Sensitivity213981Formal_StrictPositive
-- name    : Sensitivity213981Formal_StrictPositive
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T19:38:14.697993+00:00
-- url     : https://prove2.me/theorems/ee31adcf-e2fd-42c9-a1e2-02bb788abc45
-- title:
--   Strict Positive — sensitivity certificate definitions
-- statement:
--   The definitions for Strict Positive in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundConditional.strictOutHeads`, `ThreeBoundConditional.strictOutBits`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; StrictPositive.lean, lines 1–428.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_ResidualCaps
import Definitions.Def_Sensitivity213981Formal_StrictUnion
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
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
/- Refined strict conditional positive transfer, including source-labeled cap. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false

namespace ThreeBoundConditional
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open scoped BigOperators Classical
noncomputable section

variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]

def strictOutHeads (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (tl gl : L) (x : ((V × Bool) × I) → Bool) (p : V) : Finset V :=
  Finset.univ.filter fun v => S.Adj p v ∧ StrictTargetCandidate S F tl gl x v

def strictOutBits (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (tl gl : L) (x : ((V × Bool) × I) → Bool) (p : V) : Finset ((V × Bool) × I) :=
  (strictOutHeads S F tl gl x p).biUnion fun v =>
    liftBits v (S.label p v) (flipsTo (F tl) true (child x v (S.label p v)))

































end
end ThreeBoundConditional




end
end Sensitivity213981Formal


