-- Prove2me | Definitions.Def_MIPRE_Foundations_Cost_SizeProgram
-- name    : MIPRE_Foundations_Cost_SizeProgram
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:47:14.949544+00:00
-- url     : https://prove2.me/theorems/4c88e3cd-893c-40a6-af22-efb2ed4a7434
-- title:
--   Encoded size as an ambient polynomial-time program, in unary
-- statement:
--   Let `α` be a type with a size-aware encoding into the data of the ambient model, `esize a = (encode a).size` the size of the encoding of `a`, `Unary = List Unit` with `unary n = List.replicate n ()` (which encodes as the unary numeral `Data.ofNat n`), and `Prog.sizeProg` the program of an earlier bundle that computes the size of its input tree in unary, with its run lemma `sizeProg_runs`.
--
--   `MIPRE.Cost.PolyTimeFun.encodedSizeU α : PolyTimeFun α Unary` is the polynomial-time function with `toFun a := unary (esize a)`, code `Prog.sizeProg`, closedness `sizeProg_wellScoped` and time bound `(X + 1) * (5 * X + 20) + X + 6`, its `computes` field being `sizeProg_runs` at `encode a`. The one lemma, `encodedSizeU_apply`, is
--
--   $$\mathrm{encodedSizeU}\ \alpha\ (a) = \mathrm{unary}\,(\mathrm{esize}\ a).$$
--
--   This makes the size of an encoded object available to other ambient programs as a unary numeral, with output size linear in the size of the supplied encoding.
--
--   **Formalization Note**. The program counts the actual encoded tree size, so the statement holds for every `a : α`, including arbitrary malformed object-level programs when `α` is a type of encoded programs: nothing about the shape of the encoding is assumed beyond its being a tree. The definition is noncomputable because it carries a `Polynomial ℕ`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/SizeProgram.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/SizeProgram.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Reader

/-! # Encoded size as an ambient polynomial-time program -/

namespace MIPRE.Cost.PolyTimeFun

open Polynomial

/-- Count the actual encoded tree size in unary. The output size is linear in
the supplied encoding, including for arbitrary malformed object-level programs. -/
noncomputable def encodedSizeU (α : Type*) [SizedEncoding α] : PolyTimeFun α Unary where
  toFun a := unary (esize a)
  code := Prog.sizeProg
  closed := Prog.sizeProg_wellScoped
  timeBound := (X + 1) * (5 * X + 20) + X + 6
  computes a := by
    obtain ⟨t, ht, hr⟩ := Prog.sizeProg_runs (encode a)
    refine ⟨t, ?_, ?_⟩
    · simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_one, Polynomial.eval_ofNat, esize] using ht
    · simpa only [encode_unary, esize] using hr

@[simp] theorem encodedSizeU_apply {α : Type*} [SizedEncoding α] (a : α) :
    encodedSizeU α a = unary (esize a) := rfl

end MIPRE.Cost.PolyTimeFun


