-- Prove2me | Definitions.Def_MIPRE_TM_Interp_Repr
-- name    : MIPRE_TM_Interp_Repr
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:14:00.5655+00:00
-- url     : https://prove2.me/theorems/177cd3f8-d2e0-4f56-a4b9-a036525533dc
-- title:
--   Definitions of Repr: The tape representation of configurations Values as their preorder bits (`S`), the control (`ctrlRepr`), the…
-- statement:
--   The definitions of the module `MIPRE.TM.Interp.Repr` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The tape representation of configurations. Values as their preorder bits (`S`), the control (`ctrlRepr`), the environment (`envRepr`, innermost value at the right end, `#`-separated), the frames (`frameRepr`) and the stack (`kontRepr`), as lists of symbols; and their lengths in terms of the sizes.
--
--   **Definitions** (7): `MIPRE.TM.Interp.S` (A value: its preorder bits.); `MIPRE.TM.Interp.ctrlRepr` (The control: `0 · S(p.toData)` for `ev p`, `1 · S(v)` for `ret v`.); `MIPRE.TM.Interp.envRepr` (The environment `[v₁, …, vₙ]` (`v₁` innermost): `S(vₙ) # … # S(v₁) #`.); `MIPRE.TM.Interp.frameBody` (The body of a frame: the frame without its final `$`.); `MIPRE.TM.Interp.frameRepr` (A frame: its tag, its payload, `$`; a closure carries its environment after `¶`.); `MIPRE.TM.Interp.frameTag` (The two tag bits of a frame.); `MIPRE.TM.Interp.kontRepr` (The stack `[f₁, …, fₘ]` (`f₁` the top): `frameRepr fₘ ++ … ++ frameRepr f₁`.).
--
--   **Embedded lemmas** (6): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `S_nil`, `envRepr_cons`, `envRepr_nil`, `kontRepr_cons`, `kontRepr_nil`, `length_S`.
--
--   **Formalization Note** The bundle is the module `MIPRE.TM.Interp.Repr` (`MIPRE/TM/Interp/Repr.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 12 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/Interp/Repr.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/Interp/Repr.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Sign.Defs
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_TM_Interp_Instr
import Definitions.Def_MIPRE_TM_Interp_Tape

/-!
# The tape representation of configurations

Values as their preorder bits (`S`), the control (`ctrlRepr`), the environment
(`envRepr`, innermost value at the right end, `#`-separated), the frames (`frameRepr`) and
the stack (`kontRepr`), as lists of symbols; and their lengths in terms of the sizes.
-/

namespace MIPRE.TM.Interp

open MIPRE.Cost MIPRE.Cost.Machine

/-- A value: its preorder bits. -/
def S (v : Data) : List Sym := bits v.toBits

@[simp] theorem S_nil : S .nil = [.zero] := rfl

@[simp] theorem length_S (v : Data) : (S v).length = v.size := by simp [S]

/-- The control: `0 · S(p.toData)` for `ev p`, `1 · S(v)` for `ret v`. -/
def ctrlRepr : Ctrl → List Sym
  | .ev p => .zero :: S p.toData
  | .ret v => .one :: S v

/-- The environment `[v₁, …, vₙ]` (`v₁` innermost): `S(vₙ) # … # S(v₁) #`. -/
def envRepr : Env → List Sym
  | [] => []
  | v :: env => envRepr env ++ S v ++ [.sep]

@[simp] theorem envRepr_nil : envRepr [] = [] := rfl

@[simp] theorem envRepr_cons (v : Data) (env : Env) :
    envRepr (v :: env) = envRepr env ++ S v ++ [.sep] := rfl

/-- The two tag bits of a frame. -/
def frameTag : Frame → List Sym
  | .cons1 _ _ => [.zero, .zero]
  | .cons2 _ => [.zero, .one]
  | .let1 _ _ => [.one, .zero]
  | .loop1 _ _ => [.one, .one]

/-- A frame: its tag, its payload, `$`; a closure carries its environment after `¶`. -/
def frameRepr : Frame → List Sym
  | .cons1 t env => [.zero, .zero] ++ S t.toData ++ [.en] ++ envRepr env ++ [.fr]
  | .cons2 a => [.zero, .one] ++ S a ++ [.fr]
  | .let1 b env => [.one, .zero] ++ S b.toData ++ [.en] ++ envRepr env ++ [.fr]
  | .loop1 b env => [.one, .one] ++ S b.toData ++ [.en] ++ envRepr env ++ [.fr]

/-- The body of a frame: the frame without its final `$`. -/
def frameBody : Frame → List Sym
  | .cons1 t env => [.zero, .zero] ++ S t.toData ++ [.en] ++ envRepr env
  | .cons2 a => [.zero, .one] ++ S a
  | .let1 b env => [.one, .zero] ++ S b.toData ++ [.en] ++ envRepr env
  | .loop1 b env => [.one, .one] ++ S b.toData ++ [.en] ++ envRepr env

/-- The stack `[f₁, …, fₘ]` (`f₁` the top): `frameRepr fₘ ++ … ++ frameRepr f₁`. -/
def kontRepr : List Frame → List Sym
  | [] => []
  | f :: k => kontRepr k ++ frameRepr f

@[simp] theorem kontRepr_nil : kontRepr [] = [] := rfl

@[simp] theorem kontRepr_cons (f : Frame) (k : List Frame) :
    kontRepr (f :: k) = kontRepr k ++ frameRepr f := rfl

end MIPRE.TM.Interp


