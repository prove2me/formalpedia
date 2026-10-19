-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_ParserAnswers
-- name    : MIPRE_Foundations_Introspection_ParserAnswers
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:05:47.838593+00:00
-- url     : https://prove2.me/theorems/dd7b69ae-09a0-447b-8028-feaaf6bccd3c
-- title:
--   Definitions of ParserAnswers: Executable introspection answer format and internal-cutoff checks The register length `Q` and original-answer bound `R`…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.ParserAnswers` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Executable introspection answer format and internal-cutoff checks. The register length `Q` and original-answer bound `R` are supplied constants. Introspect and Sample use `pairCheck`; Read uses `tripleCheck Q R false`; Hide uses `tripleCheck Q Q true`. Exact binary tuple re-encoding rejects all malformed delimiters, extra fields, and trailing bits. The bound on the original answer is checked here, independently of any outer tuple cutoff.
--
--   **Definitions** (14): `MIPRE.Introspection.AnswerParser.instDecidablePairValid`; `MIPRE.Introspection.AnswerParser.instDecidableTripleValid`; `MIPRE.Introspection.AnswerParser.pairBits`; `MIPRE.Introspection.AnswerParser.pairBitsProg`; `MIPRE.Introspection.AnswerParser.pairCheck` (Concrete format and internal original-answer-cutoff check for Introspect/Sample.); `MIPRE.Introspection.AnswerParser.pairParts`; `MIPRE.Introspection.AnswerParser.pairPartsProg`; `MIPRE.Introspection.AnswerParser.pairValid`; `MIPRE.Introspection.AnswerParser.tripleBits`; `MIPRE.Introspection.AnswerParser.tripleBitsProg`; `MIPRE.Introspection.AnswerParser.tripleCheck` (Concrete format check for Read (`exactLast=false`) or Hide (`exactLast=true`).); `MIPRE.Introspection.AnswerParser.tripleParts`; `MIPRE.Introspection.AnswerParser.triplePartsProg`; `MIPRE.Introspection.AnswerParser.tripleValid`.
--
--   **Embedded lemmas** (9): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `pairBitsProg_apply`, `pairBits_length`, `pairPartsProg_apply`, `pairParts_pairBits`, `tripleBitsProg_apply`, `tripleBits_length`, `triplePartsProg_apply`, `tripleParts_tripleBits`, `decide_and_if`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.ParserAnswers` (`MIPRE/Foundations/Introspection/ParserAnswers.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 40 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/ParserAnswers.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/ParserAnswers.lean (definition bundle: declarations the uploaded statements rest on);
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
import Theorems.Thm_MIPRE_Cost_encode_injective

/-! # Executable introspection answer format and internal-cutoff checks

The register length `Q` and original-answer bound `R` are supplied constants.
Introspect and Sample use `pairCheck`; Read uses `tripleCheck Q R false`;
Hide uses `tripleCheck Q Q true`. Exact binary tuple re-encoding rejects all
malformed delimiters, extra fields, and trailing bits. The bound on the
original answer is checked here, independently of any outer tuple cutoff.
-/

noncomputable section

namespace MIPRE.Introspection.AnswerParser

open Cost Cost.PolyTimeFun CL.Detyping.Program
open CL.Detyping.DeciderProgram (lengthNat lengthNat_apply)

def pairBits (y a : BitStr) : BitStr := field y ++ field a

def tripleBits (y yp a : BitStr) : BitStr := field y ++ (field yp ++ field a)

@[simp] theorem pairBits_length (y a : BitStr) :
    (pairBits y a).length = 2 * (y.length + a.length + 2) := by
  simp [pairBits]; omega

@[simp] theorem tripleBits_length (y yp a : BitStr) :
    (tripleBits y yp a).length = 2 * (y.length + yp.length + a.length + 3) := by
  simp [tripleBits]; omega

def pairParts (Q : ℕ) (bs : BitStr) : BitStr × BitStr :=
  (payload (bs.take (2 * Q + 2)), payload (bs.drop (2 * Q + 2)))

def tripleParts (Q : ℕ) (bs : BitStr) : BitStr × BitStr × BitStr :=
  (payload (bs.take (2 * Q + 2)), pairParts Q (bs.drop (2 * Q + 2)))

@[simp] theorem pairParts_pairBits (Q : ℕ) (y a : BitStr) (hy : y.length = Q) :
    pairParts Q (pairBits y a) = (y, a) := by
  have hlen : (field y).length = 2 * Q + 2 := by simp [hy]
  simp [pairParts, pairBits, ← hlen]

@[simp] theorem tripleParts_tripleBits (Q : ℕ) (y yp a : BitStr)
    (hy : y.length = Q) (hyp : yp.length = Q) :
    tripleParts Q (tripleBits y yp a) = (y, yp, a) := by
  have hlen : (field y).length = 2 * Q + 2 := by simp [hy]
  simp only [tripleParts, tripleBits, ← hlen, List.take_left, payload_field,
    List.drop_left, Prod.mk.injEq, true_and]
  exact pairParts_pairBits Q yp a hyp

def pairPartsProg (Q : ℕ) : PolyTimeFun BitStr (BitStr × BitStr) :=
  (payloadProg.comp (ap₂ take (PolyTimeFun.id BitStr) (const (unary (2 * Q + 2))))).pair
    (payloadProg.comp (ap₂ drop (PolyTimeFun.id BitStr) (const (unary (2 * Q + 2)))))

@[simp] theorem pairPartsProg_apply (Q : ℕ) (bs : BitStr) :
    pairPartsProg Q bs = pairParts Q bs := by simp [pairPartsProg, pairParts]

def triplePartsProg (Q : ℕ) : PolyTimeFun BitStr (BitStr × BitStr × BitStr) :=
  (fst.comp (pairPartsProg Q)).pair
    ((pairPartsProg Q).comp (ap₂ drop (PolyTimeFun.id BitStr) (const (unary (2 * Q + 2)))))

@[simp] theorem triplePartsProg_apply (Q : ℕ) (bs : BitStr) :
    triplePartsProg Q bs = tripleParts Q bs := by
  simp [triplePartsProg, tripleParts, pairParts]

def pairBitsProg : PolyTimeFun (BitStr × BitStr) BitStr :=
  ap₂ append (fieldProg.comp fst) (fieldProg.comp snd)

@[simp] theorem pairBitsProg_apply (p : BitStr × BitStr) :
    pairBitsProg p = pairBits p.1 p.2 := rfl

def tripleBitsProg : PolyTimeFun (BitStr × BitStr × BitStr) BitStr :=
  ap₂ append (fieldProg.comp fst) (pairBitsProg.comp snd)

@[simp] theorem tripleBitsProg_apply (p : BitStr × BitStr × BitStr) :
    tripleBitsProg p = tripleBits p.1 p.2.1 p.2.2 := rfl

def pairValid (Q R : ℕ) (bs : BitStr) : Prop :=
  let p := pairParts Q bs
  bs = pairBits p.1 p.2 ∧ p.1.length = Q ∧ p.2.length ≤ R

def tripleValid (Q R : ℕ) (exactLast : Bool) (bs : BitStr) : Prop :=
  let p := tripleParts Q bs
  bs = tripleBits p.1 p.2.1 p.2.2 ∧ p.1.length = Q ∧ p.2.1.length = Q ∧
    (if exactLast then p.2.2.length = R else p.2.2.length ≤ R)

instance (Q R : ℕ) (bs : BitStr) : Decidable (pairValid Q R bs) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

instance (Q R : ℕ) (exactLast : Bool) (bs : BitStr) : Decidable (tripleValid Q R exactLast bs) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem decide_and_if (p q : Prop) [Decidable p] [Decidable q] :
    (if p then decide q else false) = decide (p ∧ q) := by
  by_cases h : p <;> simp [h]

/-- Concrete format and internal original-answer-cutoff check for Introspect/Sample. -/
def pairCheck (Q R : ℕ) : PolyTimeFun BitStr Bool :=
  let p := pairPartsProg Q
  ite (ap₂ treeEq encoded (encoded.comp (pairBitsProg.comp p)))
    (ite (ap₂ SAT.ArrayProg.eqNat (lengthNat.comp (fst.comp p)) (const Q))
      (ap₂ leNat (lengthNat.comp (snd.comp p)) (const R)) (const false)) (const false)

/-- Concrete format check for Read (`exactLast=false`) or Hide (`exactLast=true`). -/
def tripleCheck (Q R : ℕ) (exactLast : Bool) : PolyTimeFun BitStr Bool :=
  let p := triplePartsProg Q
  let finalLength := lengthNat.comp (snd.comp (snd.comp p))
  let lastCheck := if exactLast then ap₂ SAT.ArrayProg.eqNat finalLength (const R)
    else ap₂ leNat finalLength (const R)
  ite (ap₂ treeEq encoded (encoded.comp (tripleBitsProg.comp p)))
    (ite (ap₂ SAT.ArrayProg.eqNat (lengthNat.comp (fst.comp p)) (const Q))
      (ite (ap₂ SAT.ArrayProg.eqNat (lengthNat.comp (fst.comp (snd.comp p))) (const Q))
        lastCheck (const false)) (const false)) (const false)

end MIPRE.Introspection.AnswerParser

end


