-- Prove2me | Definitions.Def_MIPRE_Foundations_SAT_PcpFormat
-- name    : MIPRE_Foundations_SAT_PcpFormat
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:57:27.312985+00:00
-- url     : https://prove2.me/theorems/a5a2a19f-4019-4c9d-b5de-851e23e5a5d8
-- title:
--   Definitions of PcpFormat: Executable specification and view checks for the classical PCP
-- statement:
--   The definitions of the module `MIPRE.Foundations.SAT.PcpFormat` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Executable specification and view checks for the classical PCP
--
--   **Definitions** (6): `MIPRE.SAT.allBoolProg` (Test all supplied bits without interpreting their number as a binary magnitude.); `MIPRE.SAT.validBool` (The five finite conditions making a decider specification valid.); `MIPRE.SAT.validProg` (Uniform specification checking, including the actual encoded program size.); `MIPRE.SAT.viewFormatProg` (Check both coordinate-list lengths and every field coefficient width.); `MIPRE.SAT.widthsProg` (Check a list of coefficient widths against a binary-specified field degree.); `_private.MIPRE.Foundations.SAT.PcpFormat.0.MIPRE.SAT.andProg`.
--
--   **Embedded lemmas** (5): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `allBoolProg_apply`, `validProg_apply`, `widthsProg_apply`, `esize_bool_le`, `fold_and`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.SAT.PcpFormat` (`MIPRE/Foundations/SAT/PcpFormat.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 31 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/SAT/PcpFormat.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/PcpFormat.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_SAT_Succinct
import Definitions.Def_MIPRE_Foundations_SAT_Decoupled
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_SAT_Pcp
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_Cost_BinaryCompare
import Definitions.Def_MIPRE_Foundations_Cost_SizeProgram

/-! # Executable specification and view checks for the classical PCP -/

namespace MIPRE.SAT

open Cost Cost.PolyTimeFun Polynomial

noncomputable def andProg : PolyTimeFun (Bool × Bool) Bool :=
  congr (ite fst snd (const false)) (fun p => p.1 && p.2)
    (by rintro ⟨a, b⟩; cases a <;> rfl)

theorem fold_and (l : List Bool) (a : Bool) :
    l.foldl (fun b c => b && c) a = (a && l.all id) := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih => simp only [List.foldl_cons, ih, List.all_cons, id_eq, Bool.and_assoc]

theorem esize_bool_le (b : Bool) : esize b ≤ 3 := by cases b <;> decide

/-- Test all supplied bits without interpreting their number as a binary magnitude. -/
noncomputable def allBoolProg : PolyTimeFun (List Bool) Bool :=
  let scan := foldlAdd andProg 3 (by
    intro s a
    have hb := esize_bool_le (andProg (s, a))
    simp only [Polynomial.eval_ofNat]
    omega)
  congr (scan.comp ((PolyTimeFun.id _).pair (const true))) (fun l => l.all id) (by
    intro l
    change l.foldl (fun a b => a && b) true = _
    rw [fold_and]
    rfl)

@[simp] theorem allBoolProg_apply (l : List Bool) : allBoolProg l = l.all id := rfl

/-- Check a list of coefficient widths against a binary-specified field degree. -/
noncomputable def widthsProg : PolyTimeFun (ℕ × List BitStr) Bool :=
  let item : PolyTimeFun (BitStr × ℕ) Bool :=
    ArrayProg.eqNat.comp ((unaryToBin.comp (length.comp fst)).pair snd)
  congr (allBoolProg.comp ((mapWith item).comp (snd.pair fst)))
    (fun p => p.2.all (fun b => decide (b.length = p.1))) (by intro p; simp [item])

@[simp] theorem widthsProg_apply (p : ℕ × List BitStr) :
    widthsProg p = p.2.all (fun b => decide (b.length = p.1)) := rfl

/-- The five finite conditions making a decider specification valid. -/
def validBool (p : DescInput) : Bool :=
  decide (p.1.2.2.2.1 ≤ p.1.2.2.1) &&
  decide (2 * Nat.size p.1.2.1 ≤ p.1.2.2.1) &&
  decide (esize p.1.1 ≤ p.1.2.2.2.2) &&
  decide (p.2.1.length ≤ p.1.2.2.2.1) && decide (p.2.2.length ≤ p.1.2.2.2.1)

/-- Uniform specification checking, including the actual encoded program size. -/
noncomputable def validProg : PolyTimeFun DescInput Bool :=
  let pars : PolyTimeFun DescInput (ℕ × ℕ × ℕ × ℕ) := snd.comp fst
  let n := fst.comp pars
  let T := fst.comp (snd.comp pars)
  let Q := fst.comp (snd.comp (snd.comp pars))
  let σ := snd.comp (snd.comp (snd.comp pars))
  let bits : PolyTimeFun ℕ BitStr := ofEncodeEq Nat.bits (fun _ => rfl)
  let logBits := length.comp (bits.comp n)
  let logn := unaryToBin.comp (append.comp (logBits.pair logBits))
  let progSize := unaryToBin.comp ((encodedSizeU Prog).comp (fst.comp fst))
  let lx := unaryToBin.comp (length.comp (fst.comp snd))
  let ly := unaryToBin.comp (length.comp (snd.comp snd))
  let c₁ := leNat.comp (Q.pair T)
  let c₂ := leNat.comp (logn.pair T)
  let c₃ := leNat.comp (progSize.pair σ)
  let c₄ := leNat.comp (lx.pair Q)
  let c₅ := leNat.comp (ly.pair Q)
  congr (ap₂ andProg (ap₂ andProg (ap₂ andProg (ap₂ andProg c₁ c₂) c₃) c₄) c₅)
    validBool (by intro p; simp [andProg, c₁, c₂, c₃, c₄, c₅, pars, n, T, Q, σ,
      logn, logBits, bits, progSize, lx, ly, validBool, two_mul, Nat.size_eq_bits_len])

@[simp] theorem validProg_apply (p : DescInput) : validProg p = validBool p := rfl

/-- Check both coordinate-list lengths and every field coefficient width.
The first input pair supplies the binary degree and outer dimension. -/
noncomputable def viewFormatProg :
    PolyTimeFun ((ℕ × ℕ) × List BitStr × List BitStr) Bool :=
  let k : PolyTimeFun ((ℕ × ℕ) × List BitStr × List BitStr) ℕ := fst.comp fst
  let m := snd.comp fst
  let z := fst.comp snd
  let ev := snd.comp snd
  let lz := unaryToBin.comp (length.comp z)
  let lev := unaryToBin.comp (length.comp ev)
  let expect := addUnary.comp (m.pair (const (unary 6)))
  let lengths := ap₂ andProg (ArrayProg.eqNat.comp (lz.pair m))
    (ArrayProg.eqNat.comp (lev.pair expect))
  ap₂ andProg (ap₂ andProg lengths (widthsProg.comp (k.pair z))) (widthsProg.comp (k.pair ev))

end MIPRE.SAT


