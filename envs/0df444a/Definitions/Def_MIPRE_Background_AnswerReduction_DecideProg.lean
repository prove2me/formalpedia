-- Prove2me | Definitions.Def_MIPRE_Background_AnswerReduction_DecideProg
-- name    : MIPRE_Background_AnswerReduction_DecideProg
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T06:17:11.720223+00:00
-- url     : https://prove2.me/theorems/0ac60030-c073-43b7-be7b-0bef20fa81e0
-- title:
--   Definitions of DecideProg: The answer-reduced decision, as a program Piece AR-3e of `planning/answer-reduction.md`: polynomial-time functions…
-- statement:
--   The definitions of the module `MIPRE.Background.AnswerReduction.DecideProg` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The answer-reduced decision, as a program. Piece AR-3e of `planning/answer-reduction.md`: polynomial-time functions computing the decision on blocks of `MIPRE/Background/AnswerReduction/DecideSpec`, each with the law that it computes its specification (`verdictP_apply` for the whole). The type-dependent control is a finite table of the type pair (`PolyTimeFun.finiteFunction`); the field arithmetic is the introspection stage programs'.
--
--   **Definitions** (50): `MIPRE.AnswerReduction.LdIn` (Width, copy, test type, the two runs of blocks, polynomials and values.); `MIPRE.AnswerReduction.LvpIn` (The line, the point, the polynomials and the values.); `MIPRE.AnswerReduction.SideIn` (The parameters, the game check's verdict, the types, the blocks of the questions and of the answers.); `MIPRE.AnswerReduction.VerdictIn` (The parameters, the two game checks' verdicts, the types, the blocks of the questions and the answers.); `MIPRE.AnswerReduction.aS`; `MIPRE.AnswerReduction.ansV`; `MIPRE.AnswerReduction.bS`; `MIPRE.AnswerReduction.baseLd`; `MIPRE.AnswerReduction.blocksVP`; `MIPRE.AnswerReduction.cL`; `MIPRE.AnswerReduction.chkS`; `MIPRE.AnswerReduction.chksV`; `MIPRE.AnswerReduction.chunksProg` (**Cutting into runs**, as a program: `(n, w, l) ↦ chunks w n l`.); `MIPRE.AnswerReduction.cntP` (`cntB`, in unary, as a program.); `MIPRE.AnswerReduction.dL`; `MIPRE.AnswerReduction.decodeAmong` (Reading a value among a list of candidates, by comparing encodings; the default otherwise.); `MIPRE.AnswerReduction.descsS`; `MIPRE.AnswerReduction.dirLd`; `MIPRE.AnswerReduction.eqPart`; `MIPRE.AnswerReduction.isτL`; `MIPRE.AnswerReduction.jwL`; `MIPRE.AnswerReduction.kL`; `MIPRE.AnswerReduction.kS`; `MIPRE.AnswerReduction.ldBP` (`ldB`, as a program.); `MIPRE.AnswerReduction.ldPart`; `MIPRE.AnswerReduction.lvpBP` (`lvpB`, as a program.); `MIPRE.AnswerReduction.m'S`; `MIPRE.AnswerReduction.oL`; `MIPRE.AnswerReduction.onTys`; `MIPRE.AnswerReduction.parV`; and 16 more.
--
--   **Embedded lemmas** (8): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `chunksProg_apply`, `cntP_apply`, `decodeAmong_encode`, `ldBP_apply`, `lvpBP_apply`, `readFinite_encode`, `chunkStep_apply`, `chunkStep_fold`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.AnswerReduction.DecideProg` (`MIPRE/Background/AnswerReduction/DecideProg.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 195 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/AnswerReduction/DecideProg.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/AnswerReduction/DecideProg.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Squarefree.Basic
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
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Rotate
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.Minpoly.Finite
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
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
import Definitions.Def_MIPRE_Background_AnswerReduction_AnswerFormat
import Definitions.Def_MIPRE_Foundations_CL_Product
import Definitions.Def_MIPRE_Foundations_CL_Downsize
import Definitions.Def_MIPRE_Foundations_CL_TypedSampler
import Definitions.Def_MIPRE_Foundations_CL_ProductSampler
import Definitions.Def_MIPRE_Background_LIDT_PresentationQueries
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryConstants
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPower
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotient
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNormalize
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryDivision
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryLinear
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryElimination
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasisProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasis
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve
import Definitions.Def_MIPRE_Foundations_Cost_Iterates
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCirculantProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryKernel
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryGroupAlgebra
import Definitions.Def_MIPRE_Foundations_LowDegree_FiniteReducedComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_IdempotentSplit
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponentsProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientFrobenius
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientFactors
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryGCD
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryFactorization
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCyclotomicSeed
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySubstitution
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNonresidueLoop
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNonresidueCorrectness
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientOrbit
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryTraceBits
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOrbitPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOrbitDescent
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientTranslation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCoprimeDegree
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComposedSumPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComposedSumProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOddPrimeProgram
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPrimePowerTrace
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreier
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreierProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreierTower
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreierLoop
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryDegreeArithmetic
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryPrimality
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryPrimePower
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryDegreeFactors
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryDegreeDecomposition
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPrimePowerDispatch
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryIrreducibleAssembly
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryIrreducibleConstructor
import Definitions.Def_MIPRE_Foundations_LowDegree_Shoup
import Definitions.Def_MIPRE_Foundations_LowDegree_ShoupCoefficients
import Definitions.Def_MIPRE_Foundations_SAT_QuotientField
import Definitions.Def_MIPRE_Foundations_SAT_FieldTrace
import Definitions.Def_MIPRE_Foundations_SAT_FieldCoordinates
import Definitions.Def_MIPRE_Background_AnswerReduction_Layout
import Definitions.Def_MIPRE_Background_AnswerReduction_Family
import Definitions.Def_MIPRE_Background_AnswerReduction_TypedGame
import Definitions.Def_MIPRE_Background_AnswerReduction_Stages
import Definitions.Def_MIPRE_Background_AnswerReduction_StageLists
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_Introspection_SeedSelectorProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryFold
import Definitions.Def_MIPRE_Foundations_SAT_NormalElementProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryInverse
import Definitions.Def_MIPRE_Foundations_Introspection_LineRepresentativeProg
import Definitions.Def_MIPRE_Foundations_Cost_BinaryCompare
import Definitions.Def_MIPRE_Foundations_Introspection_SeededLineProg
import Definitions.Def_MIPRE_Foundations_Cost_TreeBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgFinite
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgParse
import Definitions.Def_MIPRE_Foundations_Introspection_BinaryBlockProg
import Definitions.Def_MIPRE_Background_AnswerReduction_StageProg
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Geometry
import Definitions.Def_MIPRE_Background_AnswerReduction_StageCorrect
import Definitions.Def_MIPRE_Foundations_CL_DetypingQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCall
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgRoute
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_CL_ProductSamplerProg
import Definitions.Def_MIPRE_Foundations_Cost_FiniteEncoding
import Definitions.Def_MIPRE_Background_AnswerReduction_PcpSampler
import Definitions.Def_MIPRE_Foundations_Introspection_FieldPolynomialProg
import Definitions.Def_MIPRE_Foundations_Introspection_FieldLineCheckProg
import Definitions.Def_MIPRE_Foundations_Introspection_PauliStageProg
import Definitions.Def_MIPRE_Foundations_Introspection_FieldQuestionProg
import Definitions.Def_MIPRE_Background_AnswerReduction_DecideSpec
import Definitions.Def_MIPRE_Foundations_Cost_SizeProgram
import Definitions.Def_MIPRE_Foundations_SAT_PcpFormat
import Definitions.Def_MIPRE_Foundations_Halting_Lists_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Repeat_Prims
import Definitions.Def_MIPRE_Foundations_Repeat_MapLoop
import Definitions.Def_MIPRE_Foundations_Repeat_Sampler
import Definitions.Def_MIPRE_Foundations_CL_Repeat
import Definitions.Def_MIPRE_Foundations_Repeat_Bits
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Pipeline_Budget
import Definitions.Def_MIPRE_Foundations_Pipeline_Repetition
import Definitions.Def_MIPRE_Foundations_Repeat_RepSampler
import Definitions.Def_MIPRE_Foundations_Repeat_Dom
import Definitions.Def_MIPRE_Foundations_Repeat_SamplerCost
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgSampler
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCost
import Definitions.Def_MIPRE_Foundations_OracularSampler
import Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderRoute
import Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderProg
import Definitions.Def_MIPRE_Foundations_CL_DetypingDecider
import Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderGame
import Definitions.Def_MIPRE_Foundations_Halting_Serial
import Definitions.Def_MIPRE_Foundations_Cost_Kleene_B
import Definitions.Def_MIPRE_Foundations_OracularDecider
import Theorems.Thm_MIPRE_Cost_encode_injective
import Theorems.Thm_MIPRE_Cost_unary_add

/-!
# The answer-reduced decision, as a program

Piece AR-3e of `planning/answer-reduction.md`: polynomial-time functions computing the decision on
blocks of `MIPRE/Background/AnswerReduction/DecideSpec`, each with the law that it computes its
specification (`verdictP_apply` for the whole). The type-dependent control is a finite table of
the type pair (`PolyTimeFun.finiteFunction`); the field arithmetic is the introspection stage
programs'.
-/

noncomputable section

namespace MIPRE.AnswerReduction

open Cost Cost.PolyTimeFun StageProg Pcp Introspection.FieldLineCheck Introspection.FieldQuestionProgram Introspection.SeededLineProgram Introspection.LineProgram CL.Detyping.Program

/-! ## Cutting a list into runs -/

def chunkStep :
    PolyTimeFun ((List BitStr × List (List BitStr)) × Unary) (List BitStr × List (List BitStr)) :=
  (drop.comp ((fst.comp fst).pair snd)).pair
    (cons (take.comp ((fst.comp fst).pair snd)) (snd.comp fst))

theorem chunkStep_apply (v : List BitStr) (vs : List (List BitStr)) (w : Unary) :
    chunkStep ((v, vs), w) = (v.drop w.length, v.take w.length :: vs) := rfl

theorem chunkStep_fold (n : ℕ) (w : Unary) (v : List BitStr) (vs : List (List BitStr)) :
    ((List.replicate n w).foldl chunkStep.step (v, vs)).2 =
      (chunks w.length n v).reverse ++ vs := by
  induction n generalizing v vs with
  | zero => simp [chunks]
  | succ n ih =>
    change ((List.replicate n w).foldl chunkStep.step
      (v.drop w.length, v.take w.length :: vs)).2 = _
    rw [ih]
    simp [chunks, List.append_assoc]

/-- **Cutting into runs**, as a program: `(n, w, l) ↦ chunks w n l`. -/
def chunksProg : PolyTimeFun (Unary × Unary × List BitStr) (List (List BitStr)) :=
  let scan := foldlAdd chunkStep 2 (by
    rintro ⟨v, vs⟩ w
    have he := esize_list_append (v.take w.length) (v.drop w.length)
    rw [List.take_append_drop] at he
    simp only [chunkStep_apply, esize_prod, esize_list_cons, Polynomial.eval_ofNat]
    omega)
  congr ((PolyTimeFun.reverse.comp snd).comp (scan.comp
    ((replicate.comp (fst.pair (fst.comp snd))).pair ((snd.comp snd).pair (const [])))))
    (fun p => chunks p.2.1.length p.1.length p.2.2) (by
      rintro ⟨n, w, v⟩
      change (((List.replicate n.length w).foldl chunkStep.step (v, [])).2).reverse = _
      rw [chunkStep_fold, List.append_nil, List.reverse_reverse])

@[simp] theorem chunksProg_apply (n w : Unary) (l : List BitStr) :
    chunksProg (n, w, l) = chunks w.length n.length l := rfl

/-! ## Reading a finite type -/

section Finite

variable {α : Type*} [SizedEncoding α] [Inhabited α]

/-- Reading a value among a list of candidates, by comparing encodings; the default otherwise. -/
def decodeAmong : List α → PolyTimeFun Data α
  | [] => const default
  | a :: as => ite (ap₂ treeEq (PolyTimeFun.id Data) (const (encode a))) (const a) (decodeAmong as)

theorem decodeAmong_encode (l : List α) (a : α) (h : a ∈ l) : decodeAmong l (encode a) = a := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    simp only [decodeAmong, PolyTimeFun.ite_apply, ap₂_apply, treeEq_apply, id_apply, const_apply]
    by_cases hb : a = b
    · subst hb; simp
    · have : (encode a : Data) ≠ encode b := fun he => hb (encode_injective he)
      simp only [this, decide_false, Bool.false_eq_true, if_false]
      exact ih ((List.mem_cons.mp h).resolve_left hb)

variable [Fintype α]

/-- **Reading a value of a finite type** off any datum. -/
def readFinite : PolyTimeFun Data α := decodeAmong Finset.univ.toList

@[simp] theorem readFinite_encode (a : α) : (readFinite : PolyTimeFun Data α) (encode a) = a :=
  decodeAmong_encode _ a (by simp)

end Finite

/-! ## The line-versus-point check -/

/-- The line, the point, the polynomials and the values. -/
abbrev LvpIn := (Unary × List BitStr × List BitStr × List BitStr) × List (List BitStr) × List BitStr

/-- `lvpB`, as a program. -/
def lvpBP : PolyTimeFun LvpIn Bool :=
  let item : PolyTimeFun ((List BitStr × BitStr) × (Unary × List BitStr × List BitStr ×
      List BitStr)) Bool := lineCheckProg.comp (snd.pair ((fst.comp fst).pair (snd.comp fst)))
  SAT.allBoolProg.comp ((mapWith item).comp ((zip.comp snd).pair fst))

@[simp] theorem lvpBP_apply (kU : Unary) (base dir pt : List BitStr) (polys : List (List BitStr))
    (vals : List BitStr) : lvpBP ((kU, base, dir, pt), polys, vals) = lvpB kU base dir pt polys vals := by
  simp only [lvpBP, comp_apply, pair_apply, fst_apply, snd_apply, mapWith_apply, zip_apply,
    SAT.allBoolProg_apply, lvpB, List.all_map]
  rfl

/-! ## The low-degree subtest of a copy -/

/-- Width, copy, test type, the two runs of blocks, polynomials and values. -/
abbrev LdIn := Unary × Desc × ℕ × Blocks × Blocks × List (List BitStr) × List BitStr

section Ld

def kL : PolyTimeFun LdIn Unary := fst
def dL : PolyTimeFun LdIn Desc := fst.comp snd
def τL : PolyTimeFun LdIn ℕ := fst.comp (snd.comp snd)
def xL : PolyTimeFun LdIn Blocks := fst.comp (snd.comp (snd.comp snd))
def yL : PolyTimeFun LdIn Blocks := fst.comp (snd.comp (snd.comp (snd.comp snd)))
def polysL : PolyTimeFun LdIn (List (List BitStr)) :=
  fst.comp (snd.comp (snd.comp (snd.comp (snd.comp snd))))
def valsL : PolyTimeFun LdIn (List BitStr) :=
  snd.comp (snd.comp (snd.comp (snd.comp (snd.comp snd))))

def oL : PolyTimeFun LdIn Unary := fst.comp dL
def szL : PolyTimeFun LdIn Unary := fst.comp (snd.comp dL)
def jwL : PolyTimeFun LdIn Unary := fst.comp (snd.comp (snd.comp dL))
def cL : PolyTimeFun LdIn Unary := snd.comp (snd.comp (snd.comp dL))

def sliceLd (l : PolyTimeFun LdIn (List BitStr)) : PolyTimeFun LdIn (List BitStr) :=
  sliceP.comp (oL.pair (szL.pair l))

def seedLd : PolyTimeFun LdIn BitStr :=
  (headD []).comp (drop.comp ((snd.comp (snd.comp yL)).pair cL))

def isτL (t : ℕ) : PolyTimeFun LdIn Bool := ap₂ SAT.ArrayProg.eqNat τL (const t)

def dirLd : PolyTimeFun LdIn (List BitStr) :=
  ite (isτL 1) (axisDirectionProg.comp ((kL.pair (jwL.pair szL)).pair seedLd))
    (selectedDirectionProg.comp ((kL.pair (jwL.pair seedLd)).pair
      (sliceLd (fst.comp (snd.comp yL)))))

def baseLd : PolyTimeFun LdIn (List BitStr) :=
  ite (isτL 1) (axisRepresentativeProg.comp ((kL.pair (jwL.pair seedLd)).pair
      (sliceLd (fst.comp yL))))
    (ite (isτL 2) (lineRepresentativeProg.comp (kL.pair ((sliceLd (fst.comp yL)).pair dirLd)))
      (sliceLd (fst.comp yL)))

/-- `ldB`, as a program. -/
def ldBP : PolyTimeFun LdIn Bool :=
  lvpBP.comp ((kL.pair (baseLd.pair (dirLd.pair (sliceLd (fst.comp xL))))).pair
    (polysL.pair valsL))

@[simp] theorem ldBP_apply (kU : Unary) (d : Desc) (τ : ℕ) (X Y : Blocks)
    (polys : List (List BitStr)) (vals : List BitStr) :
    ldBP (kU, d, τ, X, Y, polys, vals) = ldB kU d τ X Y polys vals := by
  simp only [ldBP, comp_apply, pair_apply, lvpBP_apply, ldB, kL, polysL, valsL, fst_apply,
    snd_apply, baseLd, dirLd, PolyTimeFun.ite_apply, isτL, ap₂_apply, SAT.ArrayProg.eqNat_apply,
    const_apply, decide_eq_true_eq, τL, jwL, szL, dL, seedLd, cL, yL, xL, sliceLd, sliceP_apply,
    oL, headD_apply, drop_apply, ptMapL, dirB, selDirL, seedOf]

end Ld

/-! ## The bounded parse -/

/-- The blocks a serialized answer lists, whether or not it is well formed. -/
def rawBlocks (s : BitStr) : List BitStr := (rawList (Data.parse s)).map readBits

/-- **The bounded parse**, as a program: `(k, c, s)` to whether `s` parses to `c` blocks of `k`
bits, and the blocks. -/
def parseBP : PolyTimeFun (Unary × Unary × BitStr) (Bool × List BitStr) :=
  let d := OracleDecider.parseF.comp (snd.comp snd)
  let bs := (map readBits).comp (rawListP.comp d)
  (OracleDecider.andB (OracleDecider.eqD d (encoded.comp bs))
    (OracleDecider.andB (OracleDecider.eqD (encoded.comp (length.comp bs)) (encoded.comp (fst.comp snd)))
      (SAT.widthsProg.comp ((unaryToBin.comp fst).pair bs)))).pair bs

/-! ## The number of elements -/

/-- `cntB`, in unary, as a program. -/
def cntP : PolyTimeFun ((Unary × Unary) × PcpTy) Unary :=
  let small := (finiteFunction fun t : PcpTy => decide ((t.1 : ℕ) < 5)).comp snd
  let ty (τ : LIDT.CL.Ty) := (finiteFunction fun t : PcpTy => decide (t.2 = τ)).comp snd
  let m := fst.comp fst
  let m' := snd.comp fst
  let mul (a b : PolyTimeFun ((Unary × Unary) × PcpTy) Unary) :=
    LowDegree.DegreeArithmetic.mulUnaryProg.comp (a.pair b)
  let succ (a : PolyTimeFun ((Unary × Unary) × PcpTy) Unary) := ap₂ append a (const (unary 1))
  let dm := succ (mul m (const (unary dPcp)))
  let dm' := succ (mul m' (const (unary dPcp)))
  let m6 := ap₂ append m' (const (unary 6))
  ite small (ite (ty .point) (const (unary 1)) (ite (ty .aline) (const (unary (dPcp + 1))) dm))
    (ite (ty .point) m6 (ite (ty .aline) (mul m6 (const (unary (dPcp + 1)))) (mul m6 dm')))

@[simp] theorem cntP_apply (mU m'U : Unary) (t : PcpTy) :
    cntP ((mU, m'U), t) = unary (cntB mU.length m'U.length t) := by
  obtain ⟨i, τ⟩ := t
  by_cases hi : (i : ℕ) < 5 <;> cases τ <;>
    simp [cntP, cntB, hi, ← unary_add]
  all_goals rw [unary_add, unary_length]

/-! ## One side -/

/-- The parameters, the game check's verdict, the types, the blocks of the questions and of the
answers. -/
abbrev SideIn := (Unary × Unary × List Desc) × Bool × (ArTy × ArTy) × (Blocks × Blocks) ×
  (List BitStr × List BitStr)

section Side

def kS : PolyTimeFun SideIn Unary := fst.comp fst
def m'S : PolyTimeFun SideIn Unary := fst.comp (snd.comp fst)
def descsS : PolyTimeFun SideIn (List Desc) := snd.comp (snd.comp fst)
def chkS : PolyTimeFun SideIn Bool := fst.comp snd
def tysS : PolyTimeFun SideIn (ArTy × ArTy) := fst.comp (snd.comp snd)
def xS : PolyTimeFun SideIn Blocks := fst.comp (fst.comp (snd.comp (snd.comp snd)))
def yS : PolyTimeFun SideIn Blocks := snd.comp (fst.comp (snd.comp (snd.comp snd)))
def aS : PolyTimeFun SideIn (List BitStr) := fst.comp (snd.comp (snd.comp (snd.comp snd)))
def bS : PolyTimeFun SideIn (List BitStr) := snd.comp (snd.comp (snd.comp (snd.comp snd)))

def onTys {β : Type*} [SizedEncoding β] (f : ArTy × ArTy → β) : PolyTimeFun SideIn β :=
  (finiteFunction f).comp tysS

def eqPart : PolyTimeFun SideIn Bool :=
  let idx := onTys fun pq => (eqPlan pq.1 pq.2).getD (0, 0)
  ite (onTys fun pq => (eqPlan pq.1 pq.2).isSome)
    (ap₂ SAT.ArrayProg.eqBits ((SAT.ArrayProg.getD []).comp ((fst.comp idx).pair aS))
      ((SAT.ArrayProg.getD []).comp ((snd.comp idx).pair bS)))
    (const true)

def widthP : PolyTimeFun SideIn Unary :=
  ite (onTys fun pq => decide (pq.2.2.2 = .aline)) (const (unary (dPcp + 1)))
    (ap₂ append (LowDegree.DegreeArithmetic.mulUnaryProg.comp (m'S.pair (const (unary dPcp))))
      (const (unary 1)))

def ldPart : PolyTimeFun SideIn Bool :=
  let idx := onTys fun pq => (ldPlan pq.1 pq.2).getD (0, false)
  let polys := ite (snd.comp idx)
    (chunksProg.comp ((ap₂ append m'S (const (unary 6))).pair (widthP.pair bS)))
    (cons bS (const []))
  ite (onTys fun pq => (ldPlan pq.1 pq.2).isSome)
    (ldBP.comp (kS.pair (((SAT.ArrayProg.getD default).comp ((fst.comp idx).pair descsS)).pair
      ((onTys fun pq => tyNat pq.2.2.2).pair (xS.pair (yS.pair (polys.pair aS)))))))
    (const true)

/-- `sideB`, as a program. -/
def sideBP : PolyTimeFun SideIn Bool :=
  OracleDecider.andB (OracleDecider.andB eqPart ldPart)
    (ite (onTys fun pq => chkPlan pq.1) chkS (const true))

end Side

/-! ## The predicate -/

/-- The parameters, the two game checks' verdicts, the types, the blocks of the questions and
the answers. -/
abbrev VerdictIn := (Unary × Unary × List Desc) × (Bool × Bool) × (ArTy × ArTy) ×
  (Blocks × Blocks) × (BitStr × BitStr)

section Verdict

def parV : PolyTimeFun VerdictIn (Unary × Unary × List Desc) := fst
def chksV : PolyTimeFun VerdictIn (Bool × Bool) := fst.comp snd
def tysV : PolyTimeFun VerdictIn (ArTy × ArTy) := fst.comp (snd.comp snd)
def blocksVP : PolyTimeFun VerdictIn (Blocks × Blocks) := fst.comp (snd.comp (snd.comp snd))
def ansV : PolyTimeFun VerdictIn (BitStr × BitStr) := snd.comp (snd.comp (snd.comp snd))

/-- The parse of one answer, at the type the selector names. -/
def parseV (ty : PolyTimeFun VerdictIn ArTy) (s : PolyTimeFun VerdictIn BitStr) :
    PolyTimeFun VerdictIn (Bool × List BitStr) :=
  let m := fst.comp (snd.comp ((SAT.ArrayProg.getD default).comp ((const 0).pair
    (snd.comp (snd.comp parV)))))
  parseBP.comp ((fst.comp parV).pair
    ((cntP.comp ((m.pair (fst.comp (snd.comp parV))).pair (snd.comp ty))).pair s))

/-- **`verdictB`, as a program.** -/
def verdictP : PolyTimeFun VerdictIn Bool :=
  let pa := parseV (fst.comp tysV) (fst.comp ansV)
  let pb := parseV (snd.comp tysV) (snd.comp ansV)
  let sideIn (sw : Bool) : PolyTimeFun VerdictIn SideIn :=
    let chk := if sw then snd.comp chksV else fst.comp chksV
    let tys := if sw then (snd.comp tysV).pair (fst.comp tysV) else tysV
    let bl := if sw then (snd.comp blocksVP).pair (fst.comp blocksVP) else blocksVP
    let an := if sw then (snd.comp pb).pair (snd.comp pa) else (snd.comp pa).pair (snd.comp pb)
    parV.pair (chk.pair (tys.pair (bl.pair an)))
  let sameTy := (finiteFunction fun pq : ArTy × ArTy => decide (pq.1 = pq.2)).comp tysV
  let eqAns := ite sameTy
    (OracleDecider.eqD (encoded.comp (snd.comp pa)) (encoded.comp (snd.comp pb))) (const true)
  OracleDecider.andB (fst.comp pa) (OracleDecider.andB (fst.comp pb)
    (OracleDecider.andB (OracleDecider.andB eqAns (sideBP.comp (sideIn false)))
      (sideBP.comp (sideIn true))))

end Verdict

end MIPRE.AnswerReduction

end


