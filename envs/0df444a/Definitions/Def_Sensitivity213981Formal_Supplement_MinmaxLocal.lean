-- Prove2me | Definitions.Def_Sensitivity213981Formal_Supplement_MinmaxLocal
-- name    : Sensitivity213981Formal_Supplement_MinmaxLocal
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T18:00:03.204997+00:00
-- url     : https://prove2.me/theorems/5b68a72b-53ec-4855-8491-14954b5515ce
-- title:
--   Supplement Minmax Local — sensitivity certificate definitions
-- statement:
--   The definitions for Minmax Local in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `MinmaxLocal.failures`, `MinmaxLocal.rank`, `MinmaxLocal.Row`, `MinmaxLocal.Target`, `MinmaxLocal.needed`, `MinmaxLocal.upBits`, `MinmaxLocal.downBits`, `MinmaxLocal.leftRepairBits`, `MinmaxLocal.leftDestructionBits`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; MinmaxLocal.lean, lines 1–356.

import Definitions.Def_Sensitivity213981Formal_MinmaxLocal
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





/-- The exact rank, with `-1` for the all-false state. -/
noncomputable def rank (F : Fin N → X → Prop) (x : X) : ℤ :=
  (height F x : ℤ) - 1









/-- The symmetric target: both weak predicates and at least one strong one. -/
def Target (F : Fin N → X → Prop) (t u : Fin N) (x y : X) : Prop :=
  F t x ∧ F t y ∧ (F u x ∨ F u y)















noncomputable def needed (F : Fin N → X → Prop) (t u : Fin N) (y : X) : Fin N := by
  classical
  exact if F u y then t else u











section ActualFlips
open OAI.Paper320
variable [Fintype I]

noncomputable def upBits (P : (I → Bool) → Prop) (x : I → Bool) : Finset I := by
  classical
  exact Finset.univ.filter fun a => ¬ P x ∧ P (_root_.OAI.Paper320.flip x {a})

noncomputable def downBits (P : (I → Bool) → Prop) (x : I → Bool) : Finset I := by
  classical
  exact Finset.univ.filter fun a => P x ∧ ¬ P (_root_.OAI.Paper320.flip x {a})

noncomputable def leftRepairBits (F : Fin N → (I → Bool) → Prop)
    (t u : Fin N) (x y : I → Bool) : Finset I :=
  upBits (fun z => Target F t u z y) x

noncomputable def leftDestructionBits (F : Fin N → (I → Bool) → Prop)
    (t u : Fin N) (x y : I → Bool) : Finset I :=
  downBits (fun z => Target F t u z y) x











end ActualFlips

noncomputable def failures (F : Fin N → X → Prop) (g : Fin N)
    (S : Finset J) (z : J → X) : Finset J := by
  classical
  exact S.filter fun a => F g (z a)



def Row (F : Fin N → X → Prop) (t u : ℕ → Fin N)
    (Q d : ℕ) (x y : X) : Prop :=
  d ≤  Q ∧ Target F (t d) (u d) x y









end MinmaxLocal










end
end Sensitivity213981Formal


