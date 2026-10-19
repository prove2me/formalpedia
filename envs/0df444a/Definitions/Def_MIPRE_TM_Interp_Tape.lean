-- Prove2me | Definitions.Def_MIPRE_TM_Interp_Tape
-- name    : MIPRE_TM_Interp_Tape
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:12:48.531543+00:00
-- url     : https://prove2.me/theorems/09a85f6e-5aa7-4479-a517-e5f3684c443d
-- title:
--   Definitions of Tape: Tape contents `Holds τ p l`: the tape `τ` holds the list `l` from cell `p`
-- statement:
--   The definitions of the module `MIPRE.TM.Interp.Tape` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Tape contents. `Holds τ p l`: the tape `τ` holds the list `l` from cell `p`. The lemmas relate it to appending, to writing a cell (`Function.update`) and to reading the cell under a head.
--
--   **Definitions** (6): `MIPRE.TM.Interp.BlankBefore` (The tape is blank before `p`.); `MIPRE.TM.Interp.BlankBeyond` (The tape is blank from `p` on.); `MIPRE.TM.Interp.BlankFrom` (The cells of `[p, p + n)` are blank.); `MIPRE.TM.Interp.Holds` (The tape holds `l` from cell `p`.); `MIPRE.TM.Interp.Tape` (A work tape.); `MIPRE.TM.Interp.bits` (The bits of a bit string as symbols.).
--
--   **Embedded lemmas** (5): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `nil`, `bits_append`, `bits_cons`, `bits_nil`, `length_bits`.
--
--   **Formalization Note** The bundle is the module `MIPRE.TM.Interp.Tape` (`MIPRE/TM/Interp/Tape.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 1 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/Interp/Tape.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/Interp/Tape.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Sign.Defs
import Mathlib.Tactic
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_TM_Interp_Instr

/-!
# Tape contents

`Holds τ p l`: the tape `τ` holds the list `l` from cell `p`. The lemmas relate it to
appending, to writing a cell (`Function.update`) and to reading the cell under a head.
-/

namespace MIPRE.TM.Interp

/-- A work tape. -/
abbrev Tape := ℤ → Option Sym

/-- The tape holds `l` from cell `p`. -/
def Holds (τ : Tape) (p : ℤ) (l : List Sym) : Prop :=
  ∀ k : ℕ, (hk : k < l.length) → τ (p + k) = some l[k]

namespace Holds

variable {τ : Tape} {p : ℤ}

@[simp] theorem nil : Holds τ p [] := fun k hk => by simp at hk

end Holds

/-- The cells of `[p, p + n)` are blank. -/
def BlankFrom (τ : Tape) (p : ℤ) (n : ℕ) : Prop := ∀ q, p ≤ q → q < p + n → τ q = none

/-- The tape is blank from `p` on. -/
def BlankBeyond (τ : Tape) (p : ℤ) : Prop := ∀ q, p ≤ q → τ q = none

/-- The tape is blank before `p`. -/
def BlankBefore (τ : Tape) (p : ℤ) : Prop := ∀ q, q < p → τ q = none

/-- The bits of a bit string as symbols. -/
def bits : List Bool → List Sym := List.map fun b => if b then Sym.one else Sym.zero

@[simp] theorem bits_nil : bits [] = [] := rfl
@[simp] theorem bits_cons (b : Bool) (l : List Bool) :
    bits (b :: l) = (if b then Sym.one else Sym.zero) :: bits l := rfl
@[simp] theorem bits_append (l₁ l₂ : List Bool) : bits (l₁ ++ l₂) = bits l₁ ++ bits l₂ :=
  List.map_append ..
@[simp] theorem length_bits (l : List Bool) : (bits l).length = l.length := List.length_map ..

end MIPRE.TM.Interp


