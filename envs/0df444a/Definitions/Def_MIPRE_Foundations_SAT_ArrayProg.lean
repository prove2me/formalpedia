-- Prove2me | Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
-- name    : MIPRE_Foundations_SAT_ArrayProg
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:56:05.080549+00:00
-- url     : https://prove2.me/theorems/19305495-1402-4a16-986e-4efe3413f359
-- title:
--   Definitions of ArrayProg: Equality and binary-indexed array access as ambient programs Formula variables and circuit wires are binary indices
-- statement:
--   The definitions of the module `MIPRE.Foundations.SAT.ArrayProg` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Equality and binary-indexed array access as ambient programs. Formula variables and circuit wires are binary indices. Looking them up must not first expand the index to unary: a malformed index can be exponentially larger than its encoding. The programs here scan the supplied array and compare binary indices, so their bounds apply to malformed inputs as well.
--
--   **Definitions** (8): `MIPRE.SAT.ArrayProg.eqBits` (Exact equality of bit strings, including their lengths.); `MIPRE.SAT.ArrayProg.eqNat` (Equality of binary natural numbers, without unary expansion.); `MIPRE.SAT.ArrayProg.getD` (Read a binary-indexed array, returning the fixed default outside its bounds.); `_private.MIPRE.Foundations.SAT.ArrayProg.0.MIPRE.SAT.ArrayProg.eqStep`; `_private.MIPRE.Foundations.SAT.ArrayProg.0.MIPRE.SAT.ArrayProg.eqStepP`; `_private.MIPRE.Foundations.SAT.ArrayProg.0.MIPRE.SAT.ArrayProg.finishEq`; `_private.MIPRE.Foundations.SAT.ArrayProg.0.MIPRE.SAT.ArrayProg.lookupStep`; `_private.MIPRE.Foundations.SAT.ArrayProg.0.MIPRE.SAT.ArrayProg.lookupStepP`.
--
--   **Embedded lemmas** (8): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `eqBits_apply`, `eqNat_apply`, `getD_apply`, `esize_bool_le`, `fold_eqStep`, `fold_eqStep_size`, `fold_lookupStep`, `indexed_lookup`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.SAT.ArrayProg` (`MIPRE/Foundations/SAT/ArrayProg.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 15 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/SAT/ArrayProg.lean; blueprint lem:pcp-padding-programs

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/ArrayProg.lean (definition bundle: declarations the uploaded statements rest on);
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

/-!
# Equality and binary-indexed array access as ambient programs

Formula variables and circuit wires are binary indices. Looking them up must not
first expand the index to unary: a malformed index can be exponentially larger
than its encoding. The programs here scan the supplied array and compare binary
indices, so their bounds apply to malformed inputs as well.
-/

namespace MIPRE.SAT.ArrayProg

open Cost Cost.PolyTimeFun Polynomial

def eqStep (s : BitStr × Bool) (b : Bool) : BitStr × Bool :=
  match s.1 with
  | [] => ([], false)
  | a :: as => (as, s.2 && (a == b))

def finishEq (s : BitStr × Bool) : Bool := s.2 && s.1.isEmpty

theorem esize_bool_le (b : Bool) : esize b ≤ 3 := by cases b <;> decide

theorem fold_eqStep (a b : BitStr) (ok : Bool) :
    finishEq (b.foldl eqStep (a, ok)) = (ok && decide (a = b)) := by
  induction b generalizing a ok with
  | nil => cases a <;> simp [finishEq]
  | cons b bs ih =>
    cases a with
    | nil => simp [List.foldl_cons, eqStep, ih]
    | cons a as =>
      rw [List.foldl_cons]
      simp only [eqStep, ih, List.cons.injEq]
      cases a <;> cases b <;> cases ok <;> simp

noncomputable def eqStepP : PolyTimeFun ((BitStr × Bool) × Bool) (BitStr × Bool) :=
  congr ((casesList (const ([], false))
    ((snd.comp snd).pair
      (ite (fst.comp fst)
        (ite (fst.comp snd) (snd.comp fst)
          (ite (snd.comp fst) (const false) (const true))) (const false)))).comp
      (((snd.comp fst).pair snd).pair (fst.comp fst)))
    (fun p => eqStep p.1 p.2) (by
      rintro ⟨⟨l, ok⟩, b⟩
      cases l with
      | nil => rfl
      | cons a as => cases ok <;> cases a <;> cases b <;> rfl)

theorem fold_eqStep_size (bs a : BitStr) (ok : Bool) :
    esize (bs.foldl eqStep (a, ok)) ≤ esize a + 4 := by
  induction bs generalizing a ok with
  | nil =>
    have h := esize_bool_le ok
    simp only [List.foldl_nil, esize_prod]
    omega
  | cons b bs ih =>
    cases a with
    | nil => exact ih [] false
    | cons a as =>
      have h := ih as (ok && (a == b))
      simpa only [List.foldl_cons, eqStep] using
        h.trans (by simp only [esize_list_cons]; omega)

/-- Exact equality of bit strings, including their lengths. -/
noncomputable def eqBits : PolyTimeFun (BitStr × BitStr) Bool :=
  let step := foldl eqStepP (X + C 4) (by
    rintro l ⟨a, ok⟩ pre post h
    have hb := fold_eqStep_size pre a ok
    change esize (pre.foldl eqStep (a, ok)) ≤ _
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, esize_prod]
    omega)
  let empty : PolyTimeFun BitStr Bool :=
    (casesList (const true) (const false)).comp ((const ()).pair (PolyTimeFun.id _))
  congr ((ite snd (empty.comp fst) (const false)).comp
    (step.comp (snd.pair (fst.pair (const true)))))
    (fun p => decide (p.1 = p.2)) (by
      rintro ⟨a, b⟩
      change (if (b.foldl eqStep (a, true)).2 then
        empty (b.foldl eqStep (a, true)).1 else false) = _
      have he : ∀ l, empty l = l.isEmpty := by intro l; cases l <;> rfl
      rw [he]
      have hh := fold_eqStep a b true
      cases hs : (b.foldl eqStep (a, true)).2 <;> simpa [finishEq, hs] using hh)

@[simp] theorem eqBits_apply (p : BitStr × BitStr) : eqBits p = decide (p.1 = p.2) := rfl

/-- Equality of binary natural numbers, without unary expansion. -/
noncomputable def eqNat : PolyTimeFun (ℕ × ℕ) Bool :=
  let bits : PolyTimeFun ℕ BitStr := ofEncodeEq Nat.bits (fun _ => rfl)
  congr (ap₂ eqBits (bits.comp fst) (bits.comp snd))
    (fun p => decide (p.1 = p.2)) (by
      intro p
      change decide (p.1.bits = p.2.bits) = decide (p.1 = p.2)
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      exact ⟨fun h => by simpa only [bitsVal_bits] using congrArg bitsVal h,
        fun h => congrArg Nat.bits h⟩)

@[simp] theorem eqNat_apply (p : ℕ × ℕ) : eqNat p = decide (p.1 = p.2) := rfl

section Lookup

variable {α : Type*} [SizedEncoding α]

def lookupStep (s : ℕ × α) (a : ℕ × α) : ℕ × α :=
  (s.1, if a.1 = s.1 then a.2 else s.2)

noncomputable def lookupStepP : PolyTimeFun ((ℕ × α) × (ℕ × α)) (ℕ × α) :=
  congr ((fst.comp fst).pair (ite (ap₂ eqNat (fst.comp snd) (fst.comp fst))
    (snd.comp snd) (snd.comp fst))) (fun p => lookupStep p.1 p.2) (by
      intro p
      simp only [pair_apply, comp_apply, fst_apply, PolyTimeFun.ite_apply, ap₂_apply, eqNat_apply,
        snd_apply, decide_eq_true_eq, lookupStep])

omit [SizedEncoding α] in
theorem fold_lookupStep (l : List (ℕ × α)) (k : ℕ) (d : α) :
    l.reverse.foldl lookupStep (k, d) =
      (k, l.foldr (fun a acc => if a.1 = k then a.2 else acc) d) := by
  rw [List.foldl_reverse]
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldr_cons]
    rw [ih]
    rfl

omit [SizedEncoding α] in
theorem indexed_lookup (l : List α) (base t : ℕ) (d : α) :
    ((List.range' base l.length).zip l).foldr
      (fun a acc => if a.1 = base + t then a.2 else acc) d = l.getD t d := by
  induction l generalizing base t with
  | nil => simp
  | cons a l ih =>
    cases t with
    | zero => simp [List.range'_succ]
    | succ t =>
      simp only [List.length_cons, List.range'_succ, List.zip_cons_cons, List.foldr_cons]
      rw [if_neg (by omega)]
      have he : base + (t + 1) = (base + 1) + t := by omega
      simpa only [he, List.getD_cons_succ] using ih (base + 1) t

/-- Read a binary-indexed array, returning the fixed default outside its bounds.
The scan is bounded by the array length, independently of the magnitude of the index. -/
noncomputable def getD (d : α) : PolyTimeFun (ℕ × List α) α :=
  let indexed : PolyTimeFun (List α) (List (ℕ × α)) :=
    ap₂ zip (ap₂ range'P (const 0) length) (PolyTimeFun.id _)
  let scan := foldlAdd lookupStepP X (by
    rintro ⟨k, v⟩ ⟨j, a⟩
    change esize (lookupStep (k, v) (j, a)) ≤ _
    simp only [lookupStep, esize_prod, Polynomial.eval_X]
    split_ifs <;> omega)
  congr (snd.comp (scan.comp ((reverse.comp (indexed.comp snd)).pair
    (fst.pair (const d))))) (fun p => p.2.getD p.1 d) (by
      rintro ⟨k, l⟩
      simp only [comp_apply, snd_apply, pair_apply, fst_apply, reverse_apply, scan,
        foldlAdd_apply, indexed, ap₂_apply, range'P_apply, length_apply, length_unary,
        zip_apply, id_apply, const_apply]
      change (((List.range' 0 l.length).zip l).reverse.foldl lookupStep (k, d)).2 = _
      rw [fold_lookupStep]
      simpa only [Nat.zero_add] using indexed_lookup l 0 k d)

@[simp] theorem getD_apply (d : α) (p : ℕ × List α) : getD d p = p.2.getD p.1 d := rfl

end Lookup

end MIPRE.SAT.ArrayProg


