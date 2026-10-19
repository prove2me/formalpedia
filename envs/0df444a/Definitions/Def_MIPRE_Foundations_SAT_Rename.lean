-- Prove2me | Definitions.Def_MIPRE_Foundations_SAT_Rename
-- name    : MIPRE_Foundations_SAT_Rename
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:58:11.167738+00:00
-- url     : https://prove2.me/theorems/fb4d7c2d-e2f4-40dc-9990-9fc4c4c59425
-- title:
--   Definitions of Rename: Renaming formula inputs in polynomial time The padding construction changes the offsets of the five index blocks and…
-- statement:
--   The definitions of the module `MIPRE.Foundations.SAT.Rename` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Renaming formula inputs in polynomial time. The padding construction changes the offsets of the five index blocks and their sign bits. Renaming scans the post-order serialization, applying an ambient program only at input nodes. `renameBy` uses a finite table and the binary-indexed lookup program, so its cost does not assume that all input indices are small.
--
--   **Definitions** (5): `MIPRE.SAT.Fml.Node.rename` (The serialization-level action of a renaming.); `MIPRE.SAT.Fml.rename` (Rename the input bits without changing the formula's tree.); `MIPRE.SAT.Fml.renameBy` (Rename inputs using the supplied table; an out-of-range index maps to zero.); `MIPRE.SAT.Fml.renameProg` (Any polynomial-time index transformation gives a polynomial-time formula renaming.); `_private.MIPRE.Foundations.SAT.Rename.0.MIPRE.SAT.Fml.renameNodeProg`.
--
--   **Embedded lemmas** (6): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `eval_rename`, `renameBy_apply`, `renameProg_apply`, `rpn_rename`, `size_rename`, `renameNodeProg_apply`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.SAT.Rename` (`MIPRE/Foundations/SAT/Rename.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 16 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/SAT/Rename.lean; blueprint lem:pcp-padding-programs

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/Rename.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Theorems.Thm_MIPRE_SAT_Fml_encode_fml

/-!
# Renaming formula inputs in polynomial time

The padding construction changes the offsets of the five index blocks and their
sign bits. Renaming scans the post-order serialization, applying an ambient program
only at input nodes. `renameBy` uses a finite table and the binary-indexed lookup
program, so its cost does not assume that all input indices are small.
-/

namespace MIPRE.SAT.Fml

open Cost Cost.PolyTimeFun

/-- Rename the input bits without changing the formula's tree. -/
def rename (ρ : ℕ → ℕ) : Fml → Fml
  | .inp i => .inp (ρ i)
  | .const b => .const b
  | .and f g => .and (rename ρ f) (rename ρ g)
  | .or f g => .or (rename ρ f) (rename ρ g)
  | .not f => .not (rename ρ f)

@[simp] theorem eval_rename (ρ : ℕ → ℕ) (f : Fml) (x : ℕ → Bool) :
    (rename ρ f).eval x = f.eval (x ∘ ρ) := by
  induction f <;> simp_all [rename, eval, Function.comp_def]

@[simp] theorem size_rename (ρ : ℕ → ℕ) (f : Fml) : (rename ρ f).size = f.size := by
  induction f <;> simp_all [rename, size]

/-- The serialization-level action of a renaming. -/
def Node.rename (ρ : ℕ → ℕ) : Node → Node
  | .inp i => .inp (ρ i)
  | .const b => .const b
  | .and => .and
  | .or => .or
  | .not => .not

theorem rpn_rename (ρ : ℕ → ℕ) (f : Fml) :
    (rename ρ f).rpn = f.rpn.map (Node.rename ρ) := by
  induction f <;> simp_all [rename, rpn, Node.rename]

variable {α : Type*} [SizedEncoding α]

noncomputable def renameNodeProg (R : PolyTimeFun (α × ℕ) ℕ) :
    PolyTimeFun (α × Node) Node :=
  MIPRE.SAT.PolyTimeFun.casesNode ((tagged 0 Node.inp Node.encode_inp).comp R)
    ((tagged 1 Node.const Node.encode_const).comp snd)
    (PolyTimeFun.const Node.and) (PolyTimeFun.const Node.or) (PolyTimeFun.const Node.not)

theorem renameNodeProg_apply (R : PolyTimeFun (α × ℕ) ℕ) (a : α) (nd : Node) :
    renameNodeProg R (a, nd) = Node.rename (fun i => R (a, i)) nd := by
  cases nd <;> rfl

/-- Any polynomial-time index transformation gives a polynomial-time formula renaming. -/
noncomputable def renameProg (R : PolyTimeFun (α × ℕ) ℕ) : PolyTimeFun (α × Fml) Fml :=
  PolyTimeFun.cast ((mapWith ((renameNodeProg R).comp (snd.pair fst))).comp
    ((rpnF.comp snd).pair fst)) (fun p => rename (fun i => R (p.1, i)) p.2) (by
      intro p
      simp only [comp_apply, mapWith_apply, pair_apply, fst_apply, snd_apply, rpnF_apply,
        renameNodeProg_apply, encode_fml, rpn_rename])

@[simp] theorem renameProg_apply (R : PolyTimeFun (α × ℕ) ℕ) (p : α × Fml) :
    renameProg R p = rename (fun i => R (p.1, i)) p.2 := rfl

/-- Rename inputs using the supplied table; an out-of-range index maps to zero. -/
noncomputable def renameBy : PolyTimeFun (List ℕ × Fml) Fml :=
  renameProg ((ArrayProg.getD 0).comp (snd.pair fst))

@[simp] theorem renameBy_apply (ρ : List ℕ) (f : Fml) :
    renameBy (ρ, f) = rename (fun i => ρ.getD i 0) f := rfl

end MIPRE.SAT.Fml


