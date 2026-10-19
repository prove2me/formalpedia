-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_DynamicParserSlice
-- name    : MIPRE_Foundations_Introspection_DynamicParserSlice
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:07:06.033788+00:00
-- url     : https://prove2.me/theorems/30bf6132-eb36-4216-88fe-f6df505221c6
-- title:
--   Definitions of DynamicParserSlice: Polynomial-time slicing at binary offsets The requested offset is capped by the actual input length before it is…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.DynamicParserSlice` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Polynomial-time slicing at binary offsets. The requested offset is capped by the actual input length before it is materialized as a unary scan. In particular a large binary bound does not cause an exponentially large intermediate allocation.
--
--   **Definitions** (5): `MIPRE.Introspection.DynamicParser.boundedOffset` (A uniform binary offset reader, outputting at most one unit per input bit.); `MIPRE.Introspection.DynamicParser.dropBits` (Dropping a prefix with a binary index uses the same bounded scan.); `MIPRE.Introspection.DynamicParser.takeBits` (Taking a prefix with a binary index is polynomial in the input encoding size.); `_private.MIPRE.Foundations.Introspection.DynamicParserSlice.0.MIPRE.Introspection.DynamicParser.capStep`; `_private.MIPRE.Foundations.Introspection.DynamicParserSlice.0.MIPRE.Introspection.DynamicParser.capStepFun`.
--
--   **Embedded lemmas** (6): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `boundedOffset_apply`, `dropBits_apply`, `takeBits_apply`, `capStep_apply`, `capStep_size`, `cap_fold`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.DynamicParserSlice` (`MIPRE/Foundations/Introspection/DynamicParserSlice.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 41 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/DynamicParserSlice.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/DynamicParserSlice.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_Cost_BinaryCompare
import Definitions.Def_MIPRE_Foundations_Cost_TreeBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgFinite
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgParse
import Definitions.Def_MIPRE_Foundations_CL_DetypingQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCall
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgRoute
import Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderRoute
import Definitions.Def_MIPRE_Foundations_Introspection_ParserBits
import Definitions.Def_MIPRE_Foundations_Introspection_ParserAnswers

/-! # Polynomial-time slicing at binary offsets

The requested offset is capped by the actual input length before it is
materialized as a unary scan. In particular a large binary bound does not
cause an exponentially large intermediate allocation.
-/

noncomputable section

namespace MIPRE.Introspection.DynamicParser

open Cost Cost.PolyTimeFun Polynomial

def capStepFun (s : ℕ × Unary) (_ : Bool) : ℕ × Unary :=
  if s.2.length + 1 ≤ s.1 then (s.1, () :: s.2) else s

def capStep : PolyTimeFun ((ℕ × Unary) × Bool) (ℕ × Unary) :=
  let state : PolyTimeFun ((ℕ × Unary) × Bool) (ℕ × Unary) := fst
  let num := fst.comp state
  let acc := snd.comp state
  ite (ap₂ leNat (inc.comp (unaryToBin.comp acc)) num)
    (num.pair (cons (const ()) acc)) state

theorem capStep_apply (s : ℕ × Unary) (b : Bool) :
    capStep (s, b) = capStepFun s b := by
  simp [capStep, capStepFun, PolyTimeFun.ite_apply]

theorem capStep_size (s : ℕ × Unary) (b : Bool) :
    esize (capStep (s, b)) ≤ esize s + (C 2).eval (esize b) := by
  rcases s with ⟨n, u⟩
  rw [capStep_apply]
  unfold capStepFun
  split_ifs <;> simp [esize_prod, show esize () = 1 from rfl]
  omega

theorem cap_fold (bs : BitStr) (n : ℕ) (u : Unary) (hu : u.length ≤ n) :
    bs.foldl capStepFun (n, u) = (n, unary (min n (u.length + bs.length))) := by
  induction bs generalizing u with
  | nil => simpa [Nat.min_eq_right hu] using congrArg (n, ·) (unary_length u).symm
  | cons b bs ih =>
    rw [List.foldl_cons]
    by_cases hh : u.length + 1 ≤ n
    · rw [capStepFun, if_pos hh, ih (() :: u) (by simpa using hh)]
      congr 3
      simp [Nat.add_comm, Nat.add_left_comm]
    · have he : u.length = n := by omega
      rw [capStepFun, if_neg hh, ih u hu]
      congr 2
      simp [he]

/-- A uniform binary offset reader, outputting at most one unit per input bit. -/
def boundedOffset : PolyTimeFun (BitStr × ℕ) Unary :=
  congr (snd.comp ((foldlAdd capStep (C 2) capStep_size).comp
    (fst.pair (snd.pair (const [])))))
    (fun p => unary (min p.2 p.1.length)) (by
      rintro ⟨bs, n⟩
      simpa only [comp_apply, pair_apply, fst_apply, snd_apply, const_apply,
        foldlAdd_apply, capStep_apply, List.length_nil, Nat.zero_add] using
        congrArg Prod.snd (cap_fold bs n [] (by simp)))

@[simp] theorem boundedOffset_apply (bs : BitStr) (n : ℕ) :
    boundedOffset (bs, n) = unary (min n bs.length) := rfl

/-- Taking a prefix with a binary index is polynomial in the input encoding size. -/
def takeBits : PolyTimeFun (BitStr × ℕ) BitStr := ap₂ take fst boundedOffset

@[simp] theorem takeBits_apply (bs : BitStr) (n : ℕ) : takeBits (bs, n) = bs.take n := by
  simp only [takeBits, ap₂_apply, fst_apply, boundedOffset_apply, take_apply, length_unary]
  by_cases hn : n ≤ bs.length
  · rw [Nat.min_eq_left hn]
  · rw [Nat.min_eq_right (by omega), List.take_length, List.take_of_length_le (by omega)]

/-- Dropping a prefix with a binary index uses the same bounded scan. -/
def dropBits : PolyTimeFun (BitStr × ℕ) BitStr := ap₂ drop fst boundedOffset

@[simp] theorem dropBits_apply (bs : BitStr) (n : ℕ) : dropBits (bs, n) = bs.drop n := by
  simp only [dropBits, ap₂_apply, fst_apply, boundedOffset_apply, drop_apply, length_unary]
  by_cases hn : n ≤ bs.length
  · rw [Nat.min_eq_left hn]
  · rw [Nat.min_eq_right (by omega), List.drop_length, List.drop_eq_nil_of_le (by omega)]

end MIPRE.Introspection.DynamicParser

end


