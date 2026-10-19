-- Prove2me | Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNormalize
-- name    : MIPRE_Foundations_LowDegree_BinaryNormalize
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:11:21.339206+00:00
-- url     : https://prove2.me/theorems/c00d1c14-549f-45fb-a6ce-6c5075ff7591
-- title:
--   Definitions of BinaryNormalize: Normalizing binary coefficient lists Remove trailing false coefficients by a right fold
-- statement:
--   The definitions of the module `MIPRE.Foundations.LowDegree.BinaryNormalize` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Normalizing binary coefficient lists. Remove trailing false coefficients by a right fold. The empty list represents zero; every nonzero result ends in true. Both semantics and the ambient bound hold on arbitrary coefficient lists, including redundant trailing zeros.
--
--   **Definitions** (4): `MIPRE.LowDegree.BinaryPolynomial.normalizeBits` (Canonical coefficient list, with no trailing false coefficients.); `MIPRE.LowDegree.BinaryPolynomial.normalizeBitsProg` (One fixed ambient program for canonical polynomial coefficient lists.); `MIPRE.LowDegree.BinaryPolynomial.normalizeStep` (Prepend a coefficient, suppressing zero coefficients above the leading term.); `_private.MIPRE.Foundations.LowDegree.BinaryNormalize.0.MIPRE.LowDegree.BinaryPolynomial.normalizeStepProg`.
--
--   **Embedded lemmas** (6): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `normalizeBitsProg_apply`, `normalizeBits_cons`, `normalizeBits_nil`, `fold_normalizeStep_esize`, `normalizeStep_bounded`, `normalizeStep_esize`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.LowDegree.BinaryNormalize` (`MIPRE/Foundations/LowDegree/BinaryNormalize.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 9 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryNormalize.lean; blueprint lem:binary-polynomial-normalization

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryNormalize.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial

/-!
# Normalizing binary coefficient lists

Remove trailing false coefficients by a right fold. The empty list represents
zero; every nonzero result ends in true. Both semantics and the ambient bound
hold on arbitrary coefficient lists, including redundant trailing zeros.
-/

namespace MIPRE.LowDegree.BinaryPolynomial

open Cost Cost.PolyTimeFun Polynomial

/-- Prepend a coefficient, suppressing zero coefficients above the leading term. -/
def normalizeStep (a : BitStr) (b : Bool) : BitStr :=
  if b then true :: a else if a.isEmpty then [] else false :: a

/-- Canonical coefficient list, with no trailing false coefficients. -/
def normalizeBits (a : BitStr) : BitStr := a.foldr (fun b s => normalizeStep s b) []

@[simp] theorem normalizeBits_nil : normalizeBits [] = [] := rfl

@[simp] theorem normalizeBits_cons (b : Bool) (a : BitStr) :
    normalizeBits (b :: a) = normalizeStep (normalizeBits a) b := rfl

noncomputable def normalizeStepProg : PolyTimeFun (BitStr × Bool) BitStr :=
  congr (ite snd (cons (const true) fst)
    ((casesList (const []) (cons (const false) fst)).comp (fst.pair fst)))
    (fun p => normalizeStep p.1 p.2) (by rintro ⟨a, b⟩; cases b <;> cases a <;> rfl)

theorem normalizeStep_esize (a : BitStr) (b : Bool) :
    esize (normalizeStep a b) ≤ esize a + esize b + 1 := by
  cases b <;> cases a <;> simp [normalizeStep, esize_list_cons] <;> omega

theorem fold_normalizeStep_esize (l : BitStr) (a : BitStr) :
    esize (l.foldl normalizeStep a) ≤ esize a + esize l := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
    have hs := normalizeStep_esize a b
    have hi := ih (normalizeStep a b)
    simp only [List.foldl_cons, esize_list_cons]
    omega

theorem normalizeStep_bounded : FoldBounded normalizeStepProg X := by
  intro l s pre post h
  change esize (pre.foldl normalizeStep s) ≤ _
  have hp := fold_normalizeStep_esize pre s
  have he := esize_list_append pre post
  simp only [esize_prod, Polynomial.eval_X]
  rw [← h] at he
  omega

/-- One fixed ambient program for canonical polynomial coefficient lists. -/
noncomputable def normalizeBitsProg : PolyTimeFun BitStr BitStr :=
  congr ((foldl normalizeStepProg X normalizeStep_bounded).comp
    (reverse.pair (const []))) normalizeBits (by
      intro a
      change a.reverse.foldl normalizeStep [] = a.foldr (fun b s => normalizeStep s b) []
      rw [List.foldl_reverse])

@[simp] theorem normalizeBitsProg_apply (a : BitStr) :
    normalizeBitsProg a = normalizeBits a := rfl

end MIPRE.LowDegree.BinaryPolynomial


