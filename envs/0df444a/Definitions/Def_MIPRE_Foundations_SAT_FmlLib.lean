-- Prove2me | Definitions.Def_MIPRE_Foundations_SAT_FmlLib
-- name    : MIPRE_Foundations_SAT_FmlLib
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:09:49.141982+00:00
-- url     : https://prove2.me/theorems/f5ea842c-1b29-44a8-b099-728b176947fb
-- title:
--   Definitions of FmlLib: Formulas on bit vectors The vocabulary in which the describer of the succinct Cook–Levin theorem is written…
-- statement:
--   The definitions of the module `MIPRE.Foundations.SAT.FmlLib` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Formulas on bit vectors. The vocabulary in which the describer of the succinct Cook–Levin theorem is written (`planning/succinct-cook-levin.md`, S3): a *field* is a list of formulas read as a binary number, least significant bit first (`Fml.val`); the fields of an index are slices of the input bits (`Fml.field`); and the tests on fields are conjunctions and disjunctions (`andList`, `orList`), equality with a constant or another field (`eqConst`, `eqFields`), comparison (`ltConst`, `ltFields`), addition of a constant with its carry (`addBits`, `addConstRel`), subtraction of a constant by the…
--
--   **Definitions** (27): `MIPRE.SAT.Fml.addBits` (The sum of a field and a constant (of the same length) with a carry in: the sum bits and the carry out.); `MIPRE.SAT.Fml.addConstBits` (The sum bits of a field and a constant.); `MIPRE.SAT.Fml.addConstCarry` (The carry out of the sum of a field and a constant.); `MIPRE.SAT.Fml.addConstRel` (`gs = fs + c`, exactly: the sum bits agree and there is no carry out.); `MIPRE.SAT.Fml.andList` (Conjunction of a list, as a fold.); `MIPRE.SAT.Fml.bitsOf` (The bits of a field: the values of its formulas, least significant first.); `MIPRE.SAT.Fml.constBits` (Constant bits as formulas.); `MIPRE.SAT.Fml.eqConst` (The field `fs` equals the constant `c` (of the same length).); `MIPRE.SAT.Fml.eqFStep` (The step of the equality test of two fields.); `MIPRE.SAT.Fml.eqFields` (The fields `fs` and `gs` (of the same length) are equal.); `MIPRE.SAT.Fml.eqStep` (The step of the equality test with a constant.); `MIPRE.SAT.Fml.field` (The field of `W` input bits starting at bit `a`.); `MIPRE.SAT.Fml.ltConst` (The field `fs` is below the constant `c` (of the same length).); `MIPRE.SAT.Fml.ltFStep` (The step of the comparison of two fields.); `MIPRE.SAT.Fml.ltFields` (The field `fs` is below the field `gs` (of the same length).); `MIPRE.SAT.Fml.ltStep` (The step of the comparison with a constant, least significant bit first: the prefix is below the constant's prefix iff this bit is below,…); `MIPRE.SAT.Fml.maj3` (The carry bit of a full adder.); and -1 more.
--
--   **Embedded lemmas** (5): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `bitsOf_cons`, `bitsOf_nil`, `length_bitsOf`, `length_constBits`, `length_field`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.SAT.FmlLib` (`MIPRE/Foundations/SAT/FmlLib.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 11 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/SAT/FmlLib.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/FmlLib.lean (definition bundle: declarations the uploaded statements rest on);
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

/-!
# Formulas on bit vectors

The vocabulary in which the describer of the succinct Cook–Levin theorem is written
(`planning/succinct-cook-levin.md`, S3): a *field* is a list of formulas read as a binary
number, least significant bit first (`Fml.val`); the fields of an index are slices of the
input bits (`Fml.field`); and the tests on fields are conjunctions and disjunctions
(`andList`, `orList`), equality with a constant or another field (`eqConst`, `eqFields`),
comparison (`ltConst`, `ltFields`), addition of a constant with its carry (`addBits`,
`addConstRel`), subtraction of a constant by the two's complement (`subConstBits`), padding
(`padTo`) and a multiplexer (`mux`). Every test is defined by a fold or a structural
recursion whose program is the same fold (`FmlProg.lean`), and every semantics lemma is an
equation on `val`.
-/

namespace MIPRE.SAT

open Cost

/-! ## Values of bit strings -/

/-- The bits of a number, padded to `W` bits with zeros (least significant bit first). -/
def padBits (W : ℕ) (l : BitStr) : BitStr := l ++ List.replicate (W - l.length) false

/-- The two's complement of a `W`-bit string: `2^W - v` modulo `2^W`. -/
def twosComp (c : BitStr) : BitStr := (incBits (c.map not)).take c.length

namespace Fml

/-! ## Basic connectives -/

/-- Equivalence. -/
def xnor (f g : Fml) : Fml := or (and f g) (and (not f) (not g))

/-- Exclusive or. -/
def xor (f g : Fml) : Fml := or (and f (not g)) (and (not f) g)

/-- The multiplexer `if s then a else b`. -/
def mux (s a b : Fml) : Fml := or (and s a) (and (not s) b)

/-- Conjunction of a list, as a fold. -/
def andList (l : List Fml) : Fml := l.foldl and (const true)

/-- Disjunction of a list, as a fold. -/
def orList (l : List Fml) : Fml := l.foldl or (const false)

/-! ## Fields -/

/-- The bits of a field: the values of its formulas, least significant first. -/
def bitsOf (fs : List Fml) (x : ℕ → Bool) : BitStr := fs.map (·.eval x)

/-- The value of a field. -/
def val (fs : List Fml) (x : ℕ → Bool) : ℕ := bitsVal (bitsOf fs x)

@[simp] theorem bitsOf_nil (x : ℕ → Bool) : bitsOf [] x = [] := rfl

@[simp] theorem bitsOf_cons (f : Fml) (fs : List Fml) (x : ℕ → Bool) :
    bitsOf (f :: fs) x = f.eval x :: bitsOf fs x := rfl

@[simp] theorem length_bitsOf (fs : List Fml) (x : ℕ → Bool) : (bitsOf fs x).length = fs.length :=
  List.length_map _

/-- The field of `W` input bits starting at bit `a`. -/
def field (a W : ℕ) : List Fml := (List.range' a W).map inp

@[simp] theorem length_field (a W : ℕ) : (field a W).length = W := by simp [field]

/-- Constant bits as formulas. -/
def constBits (c : BitStr) : List Fml := c.map const

@[simp] theorem length_constBits (c : BitStr) : (constBits c).length = c.length := by simp [constBits]

/-- Padding a field to `W` bits with zeros. -/
def padTo (W : ℕ) (fs : List Fml) : List Fml := fs ++ List.replicate (W - fs.length) (const false)

/-! ## Equality -/

/-- The step of the equality test with a constant. -/
def eqStep (acc : Fml) (p : Fml × Bool) : Fml := and acc (if p.2 then p.1 else not p.1)

/-- The field `fs` equals the constant `c` (of the same length). -/
def eqConst (fs : List Fml) (c : BitStr) : Fml := (fs.zip c).foldl eqStep (const true)

/-- The step of the equality test of two fields. -/
def eqFStep (acc : Fml) (p : Fml × Fml) : Fml := and acc (xnor p.1 p.2)

/-- The fields `fs` and `gs` (of the same length) are equal. -/
def eqFields (fs gs : List Fml) : Fml := (fs.zip gs).foldl eqFStep (const true)

/-! ## Comparison -/

/-- The step of the comparison with a constant, least significant bit first: the prefix is
below the constant's prefix iff this bit is below, or equal with the lower bits below. -/
def ltStep (lt : Fml) (p : Fml × Bool) : Fml :=
  or (and (not p.1) (const p.2)) (and (xnor p.1 (const p.2)) lt)

/-- The field `fs` is below the constant `c` (of the same length). -/
def ltConst (fs : List Fml) (c : BitStr) : Fml := (fs.zip c).foldl ltStep (const false)

/-- The step of the comparison of two fields. -/
def ltFStep (lt : Fml) (p : Fml × Fml) : Fml := or (and (not p.1) p.2) (and (xnor p.1 p.2) lt)

/-- The field `fs` is below the field `gs` (of the same length). -/
def ltFields (fs gs : List Fml) : Fml := (fs.zip gs).foldl ltFStep (const false)

/-! ## Addition of a constant -/

/-- The sum bit of a full adder. -/
def sum3 (f b c : Fml) : Fml := xor (xor f b) c

/-- The carry bit of a full adder. -/
def maj3 (f b c : Fml) : Fml := or (and f b) (and (or f b) c)

/-- The sum of a field and a constant (of the same length) with a carry in: the sum bits and
the carry out. -/
def addBits : List Fml → BitStr → Fml → List Fml × Fml
  | f :: fs, b :: c, cin =>
    let r := addBits fs c (maj3 f (const b) cin)
    (sum3 f (const b) cin :: r.1, r.2)
  | _, _, cin => ([], cin)

/-- The sum bits of a field and a constant. -/
def addConstBits (fs : List Fml) (c : BitStr) : List Fml := (addBits fs c (const false)).1

/-- The carry out of the sum of a field and a constant. -/
def addConstCarry (fs : List Fml) (c : BitStr) : Fml := (addBits fs c (const false)).2

/-- `gs = fs + c`, exactly: the sum bits agree and there is no carry out. -/
def addConstRel (fs gs : List Fml) (c : BitStr) : Fml :=
  and (eqFields gs (addConstBits fs c)) (not (addConstCarry fs c))

/-! ## Subtraction of a constant -/

/-- The difference `fs - c` by the two's complement, correct when `c ≤ fs`. -/
def subConstBits (fs : List Fml) (c : BitStr) : List Fml := addConstBits fs (twosComp c)

/-! ## Input bounds -/

end Fml

end MIPRE.SAT


