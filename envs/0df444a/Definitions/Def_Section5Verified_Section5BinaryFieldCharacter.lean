-- Prove2me | Definitions.Def_Section5Verified_Section5BinaryFieldCharacter
-- name    : Section5Verified_Section5BinaryFieldCharacter
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:01:28.314145+00:00
-- url     : https://prove2.me/theorems/5655e945-f552-504a-8f43-0a816cc92437
-- title:
--   Section5BinaryFieldCharacter — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5BinaryFieldCharacter; mechanically extracted with exact Lean declaration spans.

import Mathlib
section
set_option autoImplicit false

open Module

namespace Section5PowerCode

noncomputable def binaryCharacter : AddChar (ZMod 2) ℝ where
  toFun x := (-1 : ℝ)^x.val
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by
    rw [ZMod.val_add,← pow_add]
    exact (neg_one_pow_eq_pow_mod_two _).symm



noncomputable def basisCharacter {F α : Type*} [AddCommGroup F] [Module (ZMod 2) F]
    (b : Basis α (ZMod 2) F) (i : α) : AddChar F ℝ :=
  binaryCharacter.compAddMonoidHom (b.coord i).toAddMonoidHom





end Section5PowerCode

end


