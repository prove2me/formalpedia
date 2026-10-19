-- Prove2me | Definitions.Def_MIPRE_Foundations_CL_DetypingProgParse
-- name    : MIPRE_Foundations_CL_DetypingProgParse
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:58:19.762951+00:00
-- url     : https://prove2.me/theorems/aa187798-6b6e-472b-82db-708696d5a7b0
-- title:
--   Definitions of DetypingProgParse: Total parsing for the detyping sampler Raw trees are converted to canonical bit strings and binary naturals before the…
-- statement:
--   The definitions of the module `MIPRE.Foundations.CL.DetypingProgParse` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Total parsing for the detyping sampler. Raw trees are converted to canonical bit strings and binary naturals before the fixed finite graph computation. Every parser is an actual polynomial-time ambient program, including on malformed encodings.
--
--   **Definitions** (10): `MIPRE.CL.Detyping.Program.Parsed`; `MIPRE.CL.Detyping.Program.encoded`; `MIPRE.CL.Detyping.Program.parse`; `MIPRE.CL.Detyping.Program.rawList`; `MIPRE.CL.Detyping.Program.rawTruth`; `MIPRE.CL.Detyping.Program.rawTruthProg`; `MIPRE.CL.Detyping.Program.readBits`; `MIPRE.CL.Detyping.Program.readNat`; `MIPRE.CL.Detyping.Program.readVector` (Reading a fixed number of graph bits is a finite collection of array reads.); `MIPRE.CL.Detyping.Program.vectorEncoding`.
--
--   **Embedded lemmas** (3): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `encode_rawList`, `encoded_apply`, `readVector_apply`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.CL.DetypingProgParse` (`MIPRE/Foundations/CL/DetypingProgParse.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 24 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/DetypingProgParse.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/DetypingProgParse.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
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
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_Cost_TreeBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgFinite

/-! # Total parsing for the detyping sampler

Raw trees are converted to canonical bit strings and binary naturals before
the fixed finite graph computation. Every parser is an actual polynomial-time
ambient program, including on malformed encodings.
-/

namespace MIPRE.CL.Detyping.Program

open Cost Cost.PolyTimeFun Polynomial

def rawList : Data → List Data
  | .nil => []
  | .cons a b => a :: rawList b

theorem encode_rawList (d : Data) : encode (rawList d) = d := by
  induction d with
  | nil => rfl
  | cons a b iha ihb => simpa only [rawList, encode_list_cons, encode_data] using congrArg (Data.cons a) ihb

def rawTruth : Data → Bool
  | .nil => false
  | .cons _ _ => true

noncomputable def rawTruthProg : PolyTimeFun Data Bool where
  toFun := rawTruth
  code := .elim 0 .nil (.const (encode true))
  closed := by simp [Prog.WellScoped]
  timeBound := C 4
  computes d := by
    cases d with
    | nil => exact ⟨2, by simp, Eval.elim_nil (by simp) (Eval.nil _)⟩
    | cons a b => exact ⟨4, by simp, Eval.elim_cons (a := a) (b := b) (by simp) (Eval.const _ _)⟩

noncomputable def readBits : PolyTimeFun Data BitStr :=
  (map rawTruthProg).comp (ofEncodeEq rawList encode_rawList)

noncomputable def readNat : PolyTimeFun Data ℕ := bitsValue.comp readBits

noncomputable def encoded {α : Type*} [SizedEncoding α] : PolyTimeFun α Data :=
  ofEncodeEq encode (fun _ => rfl)

@[simp] theorem encoded_apply {α : Type*} [SizedEncoding α] (a : α) : encoded a = encode a := rfl

abbrev Parsed := Data × ℕ × Bool × ℕ × BitStr × BitStr

noncomputable def parse : PolyTimeFun Data Parsed :=
  let q := treeTail
  let q1 := treeTail.comp q
  let q2 := treeTail.comp q1
  let q3 := treeTail.comp q2
  treeHead.pair ((readNat.comp (treeHead.comp q)).pair
    ((rawTruthProg.comp (treeHead.comp q1)).pair
      ((readNat.comp (treeHead.comp q2)).pair
        ((readBits.comp (treeHead.comp q3)).pair (readBits.comp (treeTail.comp q3))))))

instance vectorEncoding (d : ℕ) : SizedEncoding (Fin d → 𝔽₂) where
  encode v := encode (toBits v)
  decode d' := (decode d' : Option BitStr).map (ofBits d)
  decode_encode v := by simp [SizedEncoding.decode_encode]

/-- Reading a fixed number of graph bits is a finite collection of array reads. -/
noncomputable def readVector (d : ℕ) : PolyTimeFun BitStr (Fin d → 𝔽₂) :=
  PolyTimeFun.cast (listOf ((List.finRange d).map fun i => nthD false i.val)) (ofBits d) (by
    intro l
    change encode (toBits (ofBits d l)) =
      encode (listOf ((List.finRange d).map fun i => nthD false i.val) l)
    apply congrArg (encode : BitStr → Data)
    simp only [listOf_apply, List.map_map]
    change List.ofFn (fun i => decide (ofBits d l i = 1)) = _
    rw [List.ofFn_eq_map]
    apply List.map_congr_left
    intro i hi
    simp only [Function.comp_apply, nthD_apply]
    change decide ((if l.getD i.val false then (1 : 𝔽₂) else 0) = 1) = _
    cases l.getD i.val false <;> decide)

@[simp] theorem readVector_apply (d : ℕ) (l : BitStr) : readVector d l = ofBits d l := rfl

end MIPRE.CL.Detyping.Program


