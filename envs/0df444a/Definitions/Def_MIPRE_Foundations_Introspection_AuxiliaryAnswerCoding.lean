-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryAnswerCoding
-- name    : MIPRE_Foundations_Introspection_AuxiliaryAnswerCoding
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:11:11.822532+00:00
-- url     : https://prove2.me/theorems/a3eae568-0cfd-4127-99fc-2cdbdbcbaa64
-- title:
--   Definitions of AuxiliaryAnswerCoding: Canonical auxiliary answer coding Pauli payloads are left as bytes for the separate field-aware parser
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.AuxiliaryAnswerCoding` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Canonical auxiliary answer coding. Pauli payloads are left as bytes for the separate field-aware parser. The other three answer shapes use full-register binary vectors and the existing canonical tuple syntax. Valid raw tuples re-encode exactly, so same-type byte consistency is exactly consistency of parsed answers.
--
--   **Definitions** (3): `MIPRE.Introspection.AuxiliaryAnswer.Valid` (Canonical syntax and register lengths, with the separate original-answer cutoff.); `MIPRE.Introspection.AuxiliaryAnswer.bits` (Encode full register coordinates and preserve the original answer bytes.); `MIPRE.Introspection.AuxiliaryAnswer.decode` (Total type-directed decoding; the caller checks canonical format first.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.AuxiliaryAnswerCoding` (`MIPRE/Foundations/Introspection/AuxiliaryAnswerCoding.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 84 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/AuxiliaryAnswerCoding.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AuxiliaryAnswerCoding.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
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
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_CrossConsistency_B
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_Expanded
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Parseval
import Definitions.Def_MIPRE_Foundations_Linearity
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_Pasting
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
import Definitions.Def_MIPRE_Foundations_Introspection_DynamicParserSlice
import Definitions.Def_MIPRE_Foundations_Introspection_DynamicParser
import Definitions.Def_MIPRE_Foundations_WeylEPR
import Definitions.Def_MIPRE_Foundations_Introspection_Types
import Definitions.Def_MIPRE_Foundations_Introspection_SamplingPrefix
import Definitions.Def_MIPRE_Foundations_Introspection_TwirlDistance
import Definitions.Def_MIPRE_Foundations_Introspection_LinearMeasurement
import Definitions.Def_MIPRE_Foundations_Introspection_CommutatorParseval
import Definitions.Def_MIPRE_Foundations_Introspection_BlockTwirl
import Definitions.Def_MIPRE_Foundations_Introspection_BlockPOVM
import Definitions.Def_MIPRE_Foundations_Introspection_EPR
import Definitions.Def_MIPRE_Foundations_Introspection_BlockRetention
import Definitions.Def_MIPRE_Foundations_Introspection_PauliMixing
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterTransport
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterEPR
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterMixing
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterCoordinates
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryChecks
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPredicate

/-! # Canonical auxiliary answer coding

Pauli payloads are left as bytes for the separate field-aware parser. The
other three answer shapes use full-register binary vectors and the existing
canonical tuple syntax. Valid raw tuples re-encode exactly, so same-type byte
consistency is exactly consistency of parsed answers.
-/

namespace MIPRE.Introspection.AuxiliaryAnswer
open Cost
variable {P : Type*} {Q ℓ : ℕ}

/-- Encode full register coordinates and preserve the original answer bytes. -/
def bits : ParsedAnswer (Fin Q → CL.𝔽₂) BitStr BitStr → BitStr
  | .pauli a => a
  | .pair y a => AnswerParser.pairBits (CL.toBits y) a
  | .read y yp a => AnswerParser.tripleBits (CL.toBits y) (CL.toBits yp) a
  | .hide y yp x => AnswerParser.tripleBits (CL.toBits y) (CL.toBits yp) (CL.toBits x)

/-- Total type-directed decoding; the caller checks canonical format first. -/
def decode (Q : ℕ) : QuestionType P ℓ → BitStr →
    ParsedAnswer (Fin Q → CL.𝔽₂) BitStr BitStr
  | .inl _, bs => .pauli bs
  | .inr (.introspect, _), bs | .inr (.sample, _), bs =>
      .pair (CL.ofBits Q (AnswerParser.pairParts Q bs).1) (AnswerParser.pairParts Q bs).2
  | .inr (.read, _), bs =>
      .read (CL.ofBits Q (AnswerParser.tripleParts Q bs).1)
        (CL.ofBits Q (AnswerParser.tripleParts Q bs).2.1) (AnswerParser.tripleParts Q bs).2.2
  | .inr (.hide _, _), bs =>
      .hide (CL.ofBits Q (AnswerParser.tripleParts Q bs).1)
        (CL.ofBits Q (AnswerParser.tripleParts Q bs).2.1)
        (CL.ofBits Q (AnswerParser.tripleParts Q bs).2.2)

/-- Canonical syntax and register lengths, with the separate original-answer cutoff. -/
def Valid (Q R : ℕ) : QuestionType P ℓ → BitStr → Prop
  | .inl _, _ => True
  | .inr (.introspect, _), bs | .inr (.sample, _), bs => AnswerParser.pairValid Q R bs
  | .inr (.read, _), bs => AnswerParser.tripleValid Q R false bs
  | .inr (.hide _, _), bs => AnswerParser.tripleValid Q Q true bs

end MIPRE.Introspection.AuxiliaryAnswer


