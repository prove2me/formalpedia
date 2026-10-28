-- Prove2me | Definitions.Def_Sensitivity213981Formal_MinmaxLocal
-- name    : Sensitivity213981Formal_MinmaxLocal
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T17:08:53.314042+00:00
-- url     : https://prove2.me/theorems/4fda0944-d04b-4103-aaf5-73a3738e8593
-- title:
--   Minmax Local — sensitivity certificate definitions
-- statement:
--   The definitions for Minmax Local in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `MinmaxLocal.Nested`, `MinmaxLocal.height`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; MinmaxLocal.lean, lines 1–356.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset

namespace Sensitivity213981Formal
section
/-
Unconditional local lemmas for the graded min/max sensitivity transfer.

This file proves actual predicates and actual one-coordinate-flip identities.
It does not assume a sensitivity-transfer theorem or a recursive seed theorem.
The exact rank is defined from the finite nested family, rather than supplied
as an unproved rank oracle.
-/


set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace MinmaxLocal
open scoped Classical

variable {N : ℕ} {X J I : Type}

/-- A family indexed by `Fin N` is nested from weak to strong. -/
def Nested (F : Fin N → X → Prop) : Prop :=
  ∀ i j : Fin N, i ≤ j → ∀ x : X, F j x → F i x

/-- The number one larger than the largest accepted predicate index;
    zero denotes the all-false state. -/
noncomputable def height (F : Fin N → X → Prop) (x : X) : ℕ := by
  classical
  exact Finset.univ.sup fun i : Fin N => if F i x then i.val + 1 else 0







































section ActualFlips
open OAI.Paper320
variable [Fintype I]



















end ActualFlips















end MinmaxLocal










end
end Sensitivity213981Formal


