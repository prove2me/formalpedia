-- Prove2me | Definitions.Def_Sensitivity213981Formal_HighTypeCore
-- name    : Sensitivity213981Formal_HighTypeCore
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T17:08:54.183322+00:00
-- url     : https://prove2.me/theorems/a46c1324-8a45-4211-b732-6119581bc015
-- title:
--   High Type Core — sensitivity certificate definitions
-- statement:
--   The definitions for High Type Core in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundHighTypes.Kind`, `ThreeBoundHighTypes.OfKind`, `ThreeBoundHighTypes.budget`, `ThreeBoundHighTypes.isGuard`, `ThreeBoundHighTypes.positivePrefix`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; HighTypeCore.lean, lines 1–151.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fintype.Basic

namespace Sensitivity213981Formal
section
/- The finite high-head type system depends only on exact guard counts.
It covers both equal-threshold and symmetric min/max targets, through any
fixed maximum tolerance. The cases q=2 and q=3 have 8 and 11 types. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000

namespace ThreeBoundHighTypes

abbrev Kind (q : ℕ) := Fin (3*q+2)

def OfKind (q : ℕ) (P G : ℕ → Prop) (k : Kind q) : Prop :=
  if k.val ≤ q then P k.val ∧ (k.val=0 ∨ ¬ G (k.val-1))
  else if k.val ≤ 2*q+1 then G (k.val-(q+1)) ∧ (k.val=2*q+1 ∨ ¬ P (k.val-q))
  else P (k.val-(2*q+1)) ∧ G (k.val-(2*q+2))

def budget (q : ℕ) (k : Kind q) : ℕ :=
  if k.val ≤ q then k.val else if k.val ≤ 2*q+1 then k.val-q else k.val-(2*q+1)

def isGuard (q : ℕ) (k : Kind q) : Bool := decide (q+1 ≤ k.val)

def positivePrefix (q b : ℕ) (k : Kind q) : Bool :=
  decide ((k.val ≤ q ∧ k.val ≤ b) ∨ (2*q+2 ≤ k.val ∧ k.val-(2*q+1) ≤ b))













end ThreeBoundHighTypes




end
end Sensitivity213981Formal


