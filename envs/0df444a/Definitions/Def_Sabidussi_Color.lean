-- Prove2me | Definitions.Def_Sabidussi_Color
-- name    : Sabidussi_Color
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T04:07:10.699534+00:00
-- url     : https://prove2.me/theorems/5a563f2f-dd27-482c-8a71-34f18ba0f93a
-- title:
--   Color
-- statement:
--   Definitions and structural lemmas for Color, from Upstream contributors (gexahedron/sabidussi-lean; see pinned Apache-2.0 LICENSE and README.md)'s pinned Sabidussi compatibility conjecture for finite Eulerian loop multigraphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/Color.lean

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
set_option autoImplicit true
namespace Sabidussi
open scoped BigOperators
abbrev F₂ := ZMod 2
abbrev Color := F₂ × F₂
@[simp]
theorem F₂_add_self (x : F₂) : x + x = 0 := ZModModule.add_self x
@[simp]
theorem color_add_self (x : Color) : x + x = 0 := by
  ext <;> simp
def bracket (x y : Color) : F₂ := x.1 * y.2 + x.2 * y.1
def quadratic (x : Color) : F₂ := x.1 * x.2
@[simp]
theorem bracket_apply (x y : Color) : bracket x y = x.1 * y.2 + x.2 * y.1 := rfl
@[simp]
theorem quadratic_apply (x : Color) : quadratic x = x.1 * x.2 := rfl
@[simp]
theorem bracket_zero_left (x : Color) : bracket 0 x = 0 := by
  simp [bracket]
@[simp]
theorem bracket_zero_right (x : Color) : bracket x 0 = 0 := by
  simp [bracket]
theorem bracket_add_right (x y z : Color) :
    bracket x (y + z) = bracket x y + bracket x z := by
  simp only [bracket, Prod.fst_add, Prod.snd_add]
  ring
def bracketRightHom (x : Color) : Color →+ F₂ where
  toFun := bracket x
  map_zero' := bracket_zero_right x
  map_add' := bracket_add_right x
def tripleDifference (t : Color) : Fin 3 → Color
  | ⟨0, _⟩ => t
  | ⟨1, _⟩ => (t.2, t.1 + t.2)
  | ⟨2, _⟩ => (t.1 + t.2, t.1)
def doubleDifference (t : Color) : Fin 2 → Color := fun _ ↦ t
end Sabidussi


