-- Prove2me | Definitions.Def_MIPRE_Background_AnswerReduction_Construction
-- name    : MIPRE_Background_AnswerReduction_Construction
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T07:03:45.45347+00:00
-- url     : https://prove2.me/theorems/e62d8325-58e3-44f6-8191-5965aea52ab9
-- title:
--   Definitions of Construction: The answer-reduced verifier Piece AR-3f of `planning/answer-reduction.md`, concluded: the output of answer reduction as…
-- statement:
--   The definitions of the module `MIPRE.Background.AnswerReduction.Construction` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The answer-reduced verifier. Piece AR-3f of `planning/answer-reduction.md`, concluded: the output of answer reduction as a normal form verifier (`arVerifier`), the typed answer-reduced verifier through the detyping compiler at the answer cut `cutVal` (`arCut`); its programs as polynomial-time functions of the input programs and `(λ, μ, σ)` (`arSamplerProg`, `arCompute`), the sampler's of the input sampler's alone; and its complexity clause (`arVerifier_within`), the `within` field of the `AnswerReduction` contract. The answer cut `32 (k + 1)(m' + 7)^2` is above the length `4 (k + 1) cnt + 1`…
--
--   **Definitions** (11): `MIPRE.AnswerReduction.arCompute` (**The answer-reduced decider's program** (`ComputeAnsVerifier`), from the input programs and `(λ, μ, σ)`.); `MIPRE.AnswerReduction.arCut` (**The cutoff program of answer reduction**: both cuts `cutVal`.); `MIPRE.AnswerReduction.arSamplerProg` (**The answer-reduced sampler's program**, from the input sampler's and `(λ, μ, σ)`.); `MIPRE.AnswerReduction.arVerifier` (**The answer-reduced verifier** of `V` at `(λ, μ, σ)`: the typed answer-reduced verifier through the detyping compiler, at the cutoff…); `MIPRE.AnswerReduction.cutP` (The answer cut, from the parameters `pd n`, twice.); `MIPRE.AnswerReduction.cutPF` (The cutoff program, from `(λ, μ, σ)`.); `MIPRE.AnswerReduction.cutProg` (The cutoff program: the parameter routine, then `cutP`.); `MIPRE.AnswerReduction.cutVal` (The answer cut, `32 (k + 1)(m' + 7)^2`.); `MIPRE.AnswerReduction.parPF` (The parameter routine's program, from `(λ, μ, σ)`.); `MIPRE.AnswerReduction.typedDPF` (The typed decider's program, from the input programs and `(λ, μ, σ)`.); `MIPRE.AnswerReduction.typedPF` (The typed sampler's program, from the input sampler's and `(λ, μ, σ)`.).
--
--   **Embedded lemmas** (1): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `cutP_pd`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.AnswerReduction.Construction` (`MIPRE/Background/AnswerReduction/Construction.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 207 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/AnswerReduction/Construction.lean; blueprint lem:ar-construction

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/AnswerReduction/Construction.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Background_AnswerReduction_DecideProg
import Definitions.Def_MIPRE_Foundations_Cost_While
import Definitions.Def_MIPRE_Foundations_Pipeline_UnaryArith
import Definitions.Def_MIPRE_Foundations_Pipeline_AnswerReduction
import Definitions.Def_MIPRE_Background_AnswerReduction_Params
import Definitions.Def_MIPRE_Background_AnswerReduction_ArSampler
import Definitions.Def_MIPRE_Background_AnswerReduction_ArDecider
import Definitions.Def_MIPRE_Foundations_Pipeline_PowDom
import Definitions.Def_MIPRE_Foundations_Pipeline_PowDomRun
import Definitions.Def_MIPRE_Background_AnswerReduction_ParamsCost
import Definitions.Def_MIPRE_Foundations_CL_ProductSamplerCost
import Definitions.Def_MIPRE_Foundations_CL_ProgBuild
import Theorems.Thm_MIPRE_AnswerReduction_ParRoutine_timesU_apply
import Theorems.Thm_MIPRE_AnswerReduction_parProg_closed
import Theorems.Thm_MIPRE_AnswerReduction_parProg_runs
import Theorems.Thm_MIPRE_AnswerReduction_pd_heads
import Theorems.Thm_MIPRE_AnswerReduction_total
import Theorems.Thm_MIPRE_Cost_seqProg_closed
import Theorems.Thm_MIPRE_Cost_seqProg_runs

/-!
# The answer-reduced verifier

Piece AR-3f of `planning/answer-reduction.md`, concluded: the output of answer reduction as a
normal form verifier (`arVerifier`), the typed answer-reduced verifier through the detyping
compiler at the answer cut `cutVal` (`arCut`); its programs as polynomial-time functions of the
input programs and `(λ, μ, σ)` (`arSamplerProg`, `arCompute`), the sampler's of the input sampler's
alone; and its complexity clause (`arVerifier_within`), the `within` field of the
`AnswerReduction` contract.

The answer cut `32 (k + 1)(m' + 7)^2` is above the length `4 (k + 1) cnt + 1` of the encoding of
every well-formed answer, `cnt ≤ (m' + 6)(7 m' + 1)` field elements of `k` bits
(`MIPRE/Background/AnswerReduction/AnswerFormat`), which completeness (AR-4) needs; and it is
polynomial in the PCP's parameters, which the complexity clause needs.
-/

noncomputable section

namespace MIPRE.AnswerReduction

open Cost Cost.PolyTimeFun CL CL.Detyping.Program Pipeline SAT Pcp StageProg

/-! ## The answer cut -/

/-- The answer cut, `32 (k + 1)(m' + 7)^2`. -/
def cutVal (P : PcpParams) : ℕ := 32 * ((P.k + 1) * (P.m' + 7) * (P.m' + 7))

/-- The answer cut, from the parameters `pd n`, twice. -/
def cutP : PolyTimeFun Data (ℕ × ℕ) :=
  let k1 : PolyTimeFun Data Unary := (const ()).cons (readU.comp treeHead)
  let m7 : PolyTimeFun Data Unary :=
    ap₂ append (readU.comp (treeHead.comp treeTail)) (const (unary 7))
  let L : PolyTimeFun Data Unary := (ParRoutine.timesU 32).comp
    (LowDegree.DegreeArithmetic.mulUnaryProg.comp
      ((LowDegree.DegreeArithmetic.mulUnaryProg.comp (k1.pair m7)).pair m7))
  let Ln : PolyTimeFun Data ℕ := addUnary.comp ((const 0).pair L)
  Ln.pair Ln

variable (PD : PcpDecider) (lam mu sigma : ℕ)

theorem cutP_pd (n : ℕ) :
    cutP ((family PD lam mu sigma).pd n) =
      (cutVal (arPar PD lam mu sigma n), cutVal (arPar PD lam mu sigma n)) := by
  obtain ⟨h1, h2, -⟩ := pd_heads PD lam mu sigma n
  simp only [cutP, pair_apply, comp_apply, addUnary_apply, const_apply, cons_apply, h1, h2,
    ap₂_apply, append_apply, ParRoutine.timesU_apply, LowDegree.DegreeArithmetic.mulUnaryProg_apply,
    length_unary, List.length_cons, List.length_append, cutVal]
  simp [unary]

/-- The cutoff program: the parameter routine, then `cutP`. -/
def cutProg : Prog := seqProg (parProg PD lam mu sigma) cutP.code

/-- **The cutoff program of answer reduction**: both cuts `cutVal`. -/
def arCut : CL.Detyping.CutoffProgram where
  inner n := cutVal (arPar PD lam mu sigma n)
  outer n := cutVal (arPar PD lam mu sigma n)
  prog := cutProg PD lam mu sigma
  closed := seqProg_closed (parProg_closed PD lam mu sigma) cutP.closed
  runs n := by
    obtain ⟨t, h⟩ := parProg_runs PD lam mu sigma n
    obtain ⟨t', -, h'⟩ := cutP.computes ((family PD lam mu sigma).pd n)
    rw [encode_data, cutP_pd] at h'
    exact ⟨_, seqProg_runs cutP.closed h h'⟩

/-! ## The verifier -/

/-- **The answer-reduced verifier** of `V` at `(λ, μ, σ)`: the typed answer-reduced verifier
through the detyping compiler, at the cutoff `arCut`. -/
def arVerifier {ℓ : ℕ} (V : Verifier (ℓ + 1)) : Verifier (level ℓ + 2) :=
  CL.Detyping.DeciderProgram.verifier graph (typedSampler V.sampler PD lam mu sigma)
    (typedDecider PD V lam mu sigma) (arCut PD lam mu sigma) (by unfold level; omega)
    (total PD V lam mu sigma)

/-! ## The programs, in polynomial time -/

/-- The parameter routine's program, from `(λ, μ, σ)`. -/
def parPF : PolyTimeFun (ℕ × ℕ × ℕ) Prog :=
  (PolyTimeFun.smn (ℕ × ℕ × ℕ)).comp ((const (ParRoutine.core PD)).pair (PolyTimeFun.id _))

/-- The typed sampler's program, from the input sampler's and `(λ, μ, σ)`. -/
def typedPF (ℓ : ℕ) : PolyTimeFun (Prog × ℕ × ℕ × ℕ) Prog :=
  (PolyTimeFun.smn (Prog × ℕ × Prog)).comp
    ((const (ProductSampler.core answerProg dimProg)).pair
      ((OracleSampler.samplerProgFun.comp fst).pair ((const (ℓ + 1)).pair ((parPF PD).comp snd))))

/-- **The answer-reduced sampler's program**, from the input sampler's and `(λ, μ, σ)`. -/
def arSamplerProg (ℓ : ℕ) : PolyTimeFun (Prog × ℕ × ℕ × ℕ) Prog :=
  (ProgBuild.routeOneCallF (CL.Detyping.Program.route graph)
    (CL.Detyping.Program.post (CL.Detyping.graphDim ArTy))).comp (typedPF PD ℓ)

/-- The typed decider's program, from the input programs and `(λ, μ, σ)`. -/
def typedDPF (ℓ : ℕ) : PolyTimeFun ((Prog × Prog) × ℕ × ℕ × ℕ) Prog :=
  (PolyTimeFun.smn (Prog × Prog × ℕ × ℕ × ℕ)).comp ((const (core PD ℓ)).pair
    ((fst.comp fst).pair ((snd.comp fst).pair snd)))

/-- The cutoff program, from `(λ, μ, σ)`. -/
def cutPF : PolyTimeFun (ℕ × ℕ × ℕ) Prog :=
  ProgBuild.letF.comp ((parPF PD).pair (const cutP.code))

/-- **The answer-reduced decider's program** (`ComputeAnsVerifier`), from the input programs and
`(λ, μ, σ)`. -/
def arCompute (ℓ : ℕ) : PolyTimeFun ((Prog × Prog) × ℕ × ℕ × ℕ) Prog :=
  ProgBuild.letF.comp
    (((ProgBuild.routeOneCallF CL.Detyping.DeciderProgram.dimensionRoute
        CL.Detyping.DeciderProgram.pairPost).comp ((typedPF PD ℓ).comp ((fst.comp fst).pair snd))).pair
      (ProgBuild.letF.comp
        (((ProgBuild.routeOneCallF CL.Detyping.DeciderProgram.cutoffRoute
            CL.Detyping.DeciderProgram.pairPost).comp ((cutPF PD).comp snd)).pair
          ((ProgBuild.routeOneCallF (CL.Detyping.DeciderProgram.route graph)
            CL.Detyping.DeciderProgram.post).comp (typedDPF PD ℓ)))))

/-! ## The complexity clause -/

section Within

variable (R : Polynomial ℕ)

end Within

end MIPRE.AnswerReduction

end


