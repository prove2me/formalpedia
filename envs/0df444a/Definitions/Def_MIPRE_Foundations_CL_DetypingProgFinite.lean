-- Prove2me | Definitions.Def_MIPRE_Foundations_CL_DetypingProgFinite
-- name    : MIPRE_Foundations_CL_DetypingProgFinite
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:57:17.918533+00:00
-- url     : https://prove2.me/theorems/8382d412-f267-44f4-8bd4-78396a91063a
-- title:
--   Definitions of DetypingProgFinite: Total finite query programs A fixed finite data table is an actual closed ambient program, total on every tree and…
-- statement:
--   The definitions of the module `MIPRE.Foundations.CL.DetypingProgFinite` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Total finite query programs. A fixed finite data table is an actual closed ambient program, total on every tree and polynomial in the size of that tree. The constants depend on the table; this lemma makes no uniform polynomial claim about its construction.
--
--   **Definitions** (6): `MIPRE.Cost.PolyTimeFun.finiteFunction` (Every fixed function on a finite, faithfully encoded domain has a concrete polynomial-time table program.); `MIPRE.Cost.PolyTimeFun.finiteTable` (First matching key, or `nil`.); `MIPRE.Cost.PolyTimeFun.treeEq` (Equality of arbitrary trees, through their injective serialization.); `MIPRE.Cost.PolyTimeFun.treeHead` (A tree's left child, with a fixed default for a leaf.); `MIPRE.Cost.PolyTimeFun.treePair` (Pair two raw trees.); `MIPRE.Cost.PolyTimeFun.treeTail` (A tree's right child, with a fixed default for a leaf.).
--
--   **Embedded lemmas** (7): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `finiteFunction_apply`, `finiteTable_apply_of_mem`, `treeEq_apply`, `treeHead_cons`, `treePair_apply`, `treeTail_cons`, `bits_prefix_unique`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.CL.DetypingProgFinite` (`MIPRE/Foundations/CL/DetypingProgFinite.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 17 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/DetypingProgFinite.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/DetypingProgFinite.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_Cost_TreeBits

/-! # Total finite query programs

A fixed finite data table is an actual closed ambient program, total on every
tree and polynomial in the size of that tree. The constants depend on the table;
this lemma makes no uniform polynomial claim about its construction.
-/

namespace MIPRE.Cost.PolyTimeFun

open Polynomial

theorem bits_prefix_unique (a b : Data) (xs ys : BitStr)
    (h : a.toBits ++ xs = b.toBits ++ ys) : a = b ∧ xs = ys := by
  induction a generalizing b xs ys with
  | nil =>
    cases b with
    | nil => simpa [Data.toBits] using h
    | cons b c => simp [Data.toBits] at h
  | cons a c iha ihc =>
    cases b with
    | nil => simp [Data.toBits] at h
    | cons b d =>
      have h' : a.toBits ++ (c.toBits ++ xs) = b.toBits ++ (d.toBits ++ ys) := by
        simpa [Data.toBits, List.append_assoc] using h
      obtain ⟨hab, hcd⟩ := iha b _ _ h'
      obtain ⟨hcd', hxy⟩ := ihc d xs ys hcd
      exact ⟨by rw [hab, hcd'], hxy⟩

/-- Equality of arbitrary trees, through their injective serialization. -/
noncomputable def treeEq : PolyTimeFun (Data × Data) Bool :=
  congr (ap₂ SAT.ArrayProg.eqBits (toBits.comp fst) (toBits.comp snd))
    (fun p => decide (p.1 = p.2)) (by
      intro p
      simp only [ap₂_apply, comp_apply, toBits_apply, fst_apply, snd_apply,
        SAT.ArrayProg.eqBits_apply]
      congr 1
      apply propext
      constructor
      · intro h
        exact (bits_prefix_unique p.1 p.2 [] [] (by simpa using h)).1
      · exact congrArg Data.toBits)

@[simp] theorem treeEq_apply (p : Data × Data) : treeEq p = decide (p.1 = p.2) := rfl

/-- A tree's right child, with a fixed default for a leaf. -/
noncomputable def treeTail : PolyTimeFun Data Data where
  toFun d := match d with | .nil => .nil | .cons _ b => b
  code := Prog.sndProg
  closed := Prog.sndProg_wellScoped
  timeBound := X + C 2
  computes d := by
    cases d with
    | nil => exact ⟨2, by simp, Eval.elim_nil (by simp) (Eval.nil _)⟩
    | cons a b =>
      exact ⟨b.size + 2, by simp only [esize_data, Data.size_cons,
        Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]; omega,
        Prog.sndProg_runs a b⟩

@[simp] theorem treeTail_cons (a b : Data) : treeTail (.cons a b) = b := rfl

/-- A tree's left child, with a fixed default for a leaf. -/
noncomputable def treeHead : PolyTimeFun Data Data where
  toFun d := match d with | .nil => .nil | .cons a _ => a
  code := Prog.fstProg
  closed := Prog.fstProg_wellScoped
  timeBound := X + C 2
  computes d := by
    cases d with
    | nil => exact ⟨2, by simp, Eval.elim_nil (by simp) (Eval.nil _)⟩
    | cons a b =>
      exact ⟨a.size + 2, by simp only [esize_data, Data.size_cons,
        Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]; omega,
        Prog.fstProg_runs a b⟩

@[simp] theorem treeHead_cons (a b : Data) : treeHead (.cons a b) = a := rfl

/-- Pair two raw trees. -/
noncomputable def treePair : PolyTimeFun (Data × Data) Data :=
  ofEncodeEq (fun p => Data.cons p.1 p.2) (fun _ => rfl)

@[simp] theorem treePair_apply (p : Data × Data) : treePair p = .cons p.1 p.2 := rfl

/-- First matching key, or `nil`. The function assigned to keys need not itself
be computable: only its finitely many values become constants in the program. -/
noncomputable def finiteTable (f : Data → Data) : List Data → PolyTimeFun Data Data
  | [] => const .nil
  | a :: as => ite (ap₂ treeEq (id Data) (const a)) (const (f a)) (finiteTable f as)

theorem finiteTable_apply_of_mem (f : Data → Data) (xs : List Data) (d : Data)
    (hd : d ∈ xs) : finiteTable f xs d = f d := by
  induction xs with
  | nil => simp at hd
  | cons a as ih =>
    simp only [finiteTable, ite_apply, ap₂_apply, treeEq_apply, id_apply, const_apply]
    by_cases h : d = a
    · simp [h]
    · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact ih (List.mem_cons.mp hd |>.resolve_left h)

/-- Every fixed function on a finite, faithfully encoded domain has a concrete
polynomial-time table program. No uniform bound in the domain's cardinality is asserted. -/
noncomputable def finiteFunction {α β : Type*} [Fintype α]
    [SizedEncoding α] [SizedEncoding β] (f : α → β) : PolyTimeFun α β := by
  classical
  let xs := (Finset.univ.image (encode : α → Data)).toList
  let answer := fun d => ((decode d : Option α).map (fun a => encode (f a))).getD .nil
  let table := finiteTable answer xs
  exact {
    toFun := f
    code := table.code
    closed := table.closed
    timeBound := table.timeBound
    computes := fun a => by
      obtain ⟨t, ht, hr⟩ := table.computes (encode a)
      have ha : encode a ∈ xs := by simp [xs]
      have he : table (encode a) = encode (f a) := by
        rw [finiteTable_apply_of_mem answer xs _ ha]
        simp [answer, SizedEncoding.decode_encode]
      rw [he] at hr
      exact ⟨t, ht, hr⟩ }

@[simp] theorem finiteFunction_apply {α β : Type*} [Fintype α]
    [SizedEncoding α] [SizedEncoding β] (f : α → β) (a : α) : finiteFunction f a = f a := rfl

end MIPRE.Cost.PolyTimeFun


