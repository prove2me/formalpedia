-- Prove2me | Definitions.Def_MIPRE_Background_AnswerReduction_AnswerFormat
-- name    : MIPRE_Background_AnswerReduction_AnswerFormat
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:59:55.819031+00:00
-- url     : https://prove2.me/theorems/eb2c28ef-4724-43d1-9ad2-d573452921be
-- title:
--   Definitions of AnswerFormat: The answers of the answer-reduced verifier, as bit strings Part of piece AR-3c of `planning/answer-reduction.md`: Table…
-- statement:
--   The definitions of the module `MIPRE.Background.AnswerReduction.AnswerFormat` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The answers of the answer-reduced verifier, as bit strings. Part of piece AR-3c of `planning/answer-reduction.md`: Table `tpcp` of `ld_compiler.tex`, the answer formats of the eighteen PCP types, as bit strings. An answer is a tuple of field elements of a length the type prescribes (`cnt`): one value, or the `d + 1` or `md + 1` coefficients of one polynomial, for the first five copies; `m' + 6` values, or `m' + 6` polynomials' coefficients, for the sixth. It is written as the list of the elements' `k`-bit representations, serialized as the postorder bits of its encoding (`enc`), the format…
--
--   **Definitions** (5): `MIPRE.AnswerReduction.cnt` (The number of field elements in an answer of the PCP type `t` (Table `tpcp`).); `MIPRE.AnswerReduction.elems` (The field elements of an answer, in order: the values, or the coefficients of each polynomial in turn.); `MIPRE.AnswerReduction.enc` (**The honest encoding** of an answer: its elements' `k`-bit blocks, serialized.); `MIPRE.AnswerReduction.ofElems` (An answer of the type `t` from a list of field elements.); `MIPRE.AnswerReduction.parse` (**The bounded parse** of an answer of the type `t`: a serialized list of `cnt t` blocks of `k` bits.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.AnswerReduction.AnswerFormat` (`MIPRE/Background/AnswerReduction/AnswerFormat.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 58 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/AnswerReduction/AnswerFormat.lean; blueprint def:ar-typed-game

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/AnswerReduction/AnswerFormat.lean (definition bundle: declarations the uploaded statements rest on);
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
import Mathlib.Computability.Primrec.List
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Background_LIDT_Presentation
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
import Definitions.Def_MIPRE_Background_AnswerReduction_PcpPresentation
import Definitions.Def_MIPRE_Foundations_OracularGame
import Definitions.Def_MIPRE_Background_AnswerReduction_Predicate
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_PerfectStrategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_OracularSound
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_POVMMix
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_OracularTensor
import Definitions.Def_MIPRE_Foundations_OracularComplete
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_OracularTyped

/-!
# The answers of the answer-reduced verifier, as bit strings

Part of piece AR-3c of `planning/answer-reduction.md`: Table `tpcp` of `ld_compiler.tex`, the
answer formats of the eighteen PCP types, as bit strings.

An answer is a tuple of field elements of a length the type prescribes (`cnt`): one value, or the
`d + 1` or `md + 1` coefficients of one polynomial, for the first five copies; `m' + 6` values, or
`m' + 6` polynomials' coefficients, for the sixth. It is written as the list of the elements'
`k`-bit representations, serialized as the postorder bits of its encoding (`enc`), the format the
oracularized verifier already uses for its answer pairs (`pairEnc`). Reading an answer back
(`parse`) requires the list to decode, every block to have `k` bits and the count to be the
type's; a failed parse is rejected by the typed predicate, which is the format preamble of
`fig:decider-pcp` with its length bounds.

`parse_enc` is the round trip for an answer of the right format, and `length_enc_le` the bound
on the length of an honest answer: what completeness needs.
-/

noncomputable section

namespace MIPRE.AnswerReduction

open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT Pcp Cost

variable {P : PcpParams} {k : ℕ} (E : BinField k)

/-! ## The number of field elements of an answer -/

variable (P) in
/-- The number of field elements in an answer of the PCP type `t` (Table `tpcp`). -/
def cnt (t : PcpTy) : ℕ :=
  if (t.1 : ℕ) < 5 then
    match t.2 with
    | .point => 1
    | .aline => dPcp + 1
    | .dline => P.m * dPcp + 1
  else
    match t.2 with
    | .point => P.m' + 6
    | .aline => (P.m' + 6) * (dPcp + 1)
    | .dline => (P.m' + 6) * (P.m' * dPcp + 1)

/-- The field elements of an answer, in order: the values, or the coefficients of each
polynomial in turn. -/
def elems : Ans P E.carrier → List E.carrier
  | .inl (.values a) => [a 0]
  | .inl (.apolys f) => List.ofFn (f 0)
  | .inl (.dpolys f) => List.ofFn (f 0)
  | .inr (.values a) => List.ofFn a
  | .inr (.apolys f) => List.ofFn fun r => f (finProdFinEquiv.symm r).1 (finProdFinEquiv.symm r).2
  | .inr (.dpolys f) => List.ofFn fun r => f (finProdFinEquiv.symm r).1 (finProdFinEquiv.symm r).2

/-- An answer of the type `t` from a list of field elements. -/
def ofElems (t : PcpTy) (l : List E.carrier) : Ans P E.carrier :=
  if (t.1 : ℕ) < 5 then
    .inl <| match t.2 with
      | .point => .values fun _ => l.getD 0 0
      | .aline => .apolys fun _ j => l.getD j 0
      | .dline => .dpolys fun _ j => l.getD j 0
  else
    .inr <| match t.2 with
      | .point => .values fun c => l.getD c 0
      | .aline => .apolys fun c j => l.getD (finProdFinEquiv (c, j)) 0
      | .dline => .dpolys fun c j => l.getD (finProdFinEquiv (c, j)) 0

/-! ## Bit strings -/

/-- **The honest encoding** of an answer: its elements' `k`-bit blocks, serialized. -/
def enc (a : Ans P E.carrier) : BitStr :=
  (encode ((elems E a).map E.toBits) : Data).toBitsPost

/-- **The bounded parse** of an answer of the type `t`: a serialized list of `cnt t` blocks of
`k` bits. -/
def parse (t : PcpTy) (s : BitStr) : Option (Ans P E.carrier) :=
  match (decode (Data.parse s) : Option (List BitStr)) with
  | some bs =>
    if bs.length = cnt P t ∧ ∀ b ∈ bs, b.length = k then some (ofElems E t (bs.map E.ofBits))
    else none
  | none => none

end MIPRE.AnswerReduction

end


