-- Prove2me | Definitions.Def_MIPRE_Background_AnswerReduction_ArDecider
-- name    : MIPRE_Background_AnswerReduction_ArDecider
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T06:48:13.166979+00:00
-- url     : https://prove2.me/theorems/85ea9da0-f136-4829-ae91-27171ad10b7b
-- title:
--   Definitions of ArDecider: The typed answer-reduced decider Piece AR-3e of `planning/answer-reduction.md`, concluded: the decider of the typed…
-- statement:
--   The definitions of the module `MIPRE.Background.AnswerReduction.ArDecider` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The typed answer-reduced decider. Piece AR-3e of `planning/answer-reduction.md`, concluded: the decider of the typed answer-reduced verifier as a total `CL.TypedDecider` over the types `Role × PcpTy`, whose acceptance law is the typed predicate `typedPred` of `MIPRE/Background/AnswerReduction/TypedGame` with the game check `gameCheck` (`accepts_iff`). The decider is `hardcode core (S̄, D̄, λ, μ, σ)`, one fixed program with the input programs and the parameters as data. On a typed input `(n, u, x, v, y, a, b)` it runs eight stages, each keeping its input as context: 1. the PCP parameters `pd…
--
--   **Definitions** (38): `MIPRE.AnswerReduction.aBl` (The parse of an answer into blocks, at a type.); `MIPRE.AnswerReduction.aBlocks` (The answer blocks of the answer in field `ia`, parsed at the type in field `it`.); `MIPRE.AnswerReduction.argMarg` (A marginal call's argument, after `j` stages: the input sampler's program and the query `(n, marginal w (ℓ + 1) z)` at the oracle half `z`…); `MIPRE.AnswerReduction.argPar` (Stage 1's argument: `((λ, μ, σ), n)`.); `MIPRE.AnswerReduction.argVer` (A game check's argument, after `j` stages (`j = 6, 7`): the PCP verifier's input on the question in field `i`, the answer in field `ia` and…); `MIPRE.AnswerReduction.blocksOfP` (The runs of blocks of a PCP half: `(k, m', z) ↦ blocksOf k m' z`.); `MIPRE.AnswerReduction.chk` (The game check of the typed game at index `n`.); `MIPRE.AnswerReduction.chkV` (A game check's verdict.); `MIPRE.AnswerReduction.core` (**The core of the answer-reduced decider**, on `((S̄, D̄, λ, μ, σ), (n, u, x, v, y, a, b))`.); `MIPRE.AnswerReduction.ctx0` (The core's input.); `MIPRE.AnswerReduction.ctx1` (The contexts after each stage.); `MIPRE.AnswerReduction.ctx2`; `MIPRE.AnswerReduction.ctx6`; `MIPRE.AnswerReduction.ctx7`; `MIPRE.AnswerReduction.ctx8`; `MIPRE.AnswerReduction.dB` (The width of the PCP half at index `n`.); `MIPRE.AnswerReduction.dpD`; `MIPRE.AnswerReduction.hdat` (The input tuple and the hardcoded data, after `j` stages.); `MIPRE.AnswerReduction.inp`; `MIPRE.AnswerReduction.inpLast`; and 3 more.
--
--   **Embedded lemmas** (5): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `blocksOfP_apply`, `core_closed`, `stg_closed`, `tails_cons`, `tails_zero`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.AnswerReduction.ArDecider` (`MIPRE/Background/AnswerReduction/ArDecider.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 201 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/AnswerReduction/ArDecider.lean; blueprint lem:ar-typed-decider

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/AnswerReduction/ArDecider.lean (definition bundle: declarations the uploaded statements rest on);
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
import Theorems.Thm_MIPRE_Cost_Eval_deterministic
import Theorems.Thm_MIPRE_Cost_encode_injective
import Theorems.Thm_MIPRE_Cost_hardcode_time
import Theorems.Thm_MIPRE_Cost_hardcode_time_rev
import Theorems.Thm_MIPRE_Cost_hardcode_wellScoped
import Theorems.Thm_MIPRE_AnswerReduction_ParRoutine_budCore_closed
import Theorems.Thm_MIPRE_AnswerReduction_ParRoutine_core_closed
import Theorems.Thm_MIPRE_Cost_seqProg_closed
import Theorems.Thm_MIPRE_Introspection_BinaryBlock_splitBlocksProg_apply
import Theorems.Thm_MIPRE_Pipeline_stageProg_closed

/-!
# The typed answer-reduced decider

Piece AR-3e of `planning/answer-reduction.md`, concluded: the decider of the typed answer-reduced
verifier as a total `CL.TypedDecider` over the types `Role × PcpTy`, whose acceptance law is the
typed predicate `typedPred` of `MIPRE/Background/AnswerReduction/TypedGame` with the game check
`gameCheck` (`accepts_iff`).

The decider is `hardcode core (S̄, D̄, λ, μ, σ)`, one fixed program with the input programs and the
parameters as data. On a typed input `(n, u, x, v, y, a, b)` it runs eight stages, each keeping
its input as context:

1. the PCP parameters `pd n`, by the parameter routine of the sampler (`ParRoutine.core`);
2. `Q = (λn + 1)^μ` and `T = 2^{(Q + 5)(μ + 1)}` (`ParRoutine.budCore`);
3. to 6. the input sampler's full marginals `L^𝖠 x_O`, `L^𝖡 x_O`, `L^𝖠 y_O`, `L^𝖡 y_O` of the
   oracle halves of the two questions, through the universal machine;
7. and 8. the PCP verifier of `PD` on each question's game-check view;

and decides by the program `verdictP` of `MIPRE/Background/AnswerReduction/DecideProg` on what
it read. Unlike the oracularized decider it never runs the input decider, whose program only
enters the PCP verifier's input as data, and every stage halts on every input: the parsing
stages are total, the input sampler halts on every input (`Sampler.halts`), and the PCP
verifier runs on the encoding of a genuine input. So no clock is needed (`total`).
-/

noncomputable section

namespace MIPRE.AnswerReduction

open Cost Cost.PolyTimeFun CL CL.Detyping.Program Pipeline SAT Pcp StageProg ParRoutine

/-! ## Stages -/

/-- A stage: run `p` on an argument read off the context, and keep the context. -/
def stg (arg : PolyTimeFun Data Data) (p : Prog) : Prog :=
  stageProg (ap₂ treePair arg (PolyTimeFun.id Data)) p postKeep

theorem stg_closed (arg : PolyTimeFun Data Data) {p : Prog} (hp : p.WellScoped 1) :
    (stg arg p).WellScoped 1 :=
  stageProg_closed _ hp _

/-! ## Reading the context -/

/-- The context `k` stages back. -/
def tails : ℕ → PolyTimeFun Data Data
  | 0 => PolyTimeFun.id Data
  | k + 1 => (tails k).comp treeTail

@[simp] theorem tails_zero (d : Data) : tails 0 d = d := rfl

@[simp] theorem tails_cons (k : ℕ) (a d : Data) : tails (k + 1) (.cons a d) = tails k d := by
  simp [tails, treeTail_cons]

/-- The result of the stage `k` stages back. -/
def res (k : ℕ) : PolyTimeFun Data Data := treeHead.comp (tails k)

/-- The input tuple and the hardcoded data, after `j` stages. -/
def hdat (j : ℕ) : PolyTimeFun Data Data := treeHead.comp (tails j)
def inp (j i : ℕ) : PolyTimeFun Data Data := treeHead.comp ((tails i).comp (treeTail.comp (tails j)))
def inpLast (j : ℕ) : PolyTimeFun Data Data := (tails 6).comp (treeTail.comp (tails j))

def spD (j : ℕ) : PolyTimeFun Data Data := treeHead.comp (hdat j)
def dpD (j : ℕ) : PolyTimeFun Data Data := treeHead.comp (treeTail.comp (hdat j))
def lmsD (j : ℕ) : PolyTimeFun Data Data := treeTail.comp (treeTail.comp (hdat j))

/-- The first `|x| - d` bits: the oracle half. -/
def leftBP : PolyTimeFun (BitStr × Unary) BitStr :=
  reverse.comp (drop.comp ((reverse.comp fst).pair snd))

/-- The last `d` bits: the PCP half. -/
def rightBP : PolyTimeFun (BitStr × Unary) BitStr :=
  reverse.comp (take.comp ((reverse.comp fst).pair snd))

/-- The runs of blocks of a PCP half: `(k, m', z) ↦ blocksOf k m' z`. -/
def blocksOfP : PolyTimeFun (Unary × Unary × BitStr) Blocks :=
  let n := ap₂ append (fst.comp snd) (ap₂ append (fst.comp snd) (const (unary 6)))
  let l := Introspection.BinaryBlock.splitBlocksProg.comp (n.pair (fst.pair (snd.comp snd)))
  (take.comp (l.pair (fst.comp snd))).pair ((take.comp ((drop.comp (l.pair (fst.comp snd))).pair
    (fst.comp snd))).pair (drop.comp ((drop.comp (l.pair (fst.comp snd))).pair (fst.comp snd))))

@[simp] theorem blocksOfP_apply (k m' : Unary) (z : BitStr) :
    blocksOfP (k, m', z) = blocksOf k m' z := by
  simp only [blocksOfP, blocksOf, pair_apply, comp_apply, take_apply, drop_apply, ap₂_apply,
    append_apply, const_apply, fst_apply, snd_apply,
    Introspection.BinaryBlock.splitBlocksProg_apply, List.length_append, length_unary]

/-! ## The stages -/

instance : Inhabited LIDT.CL.Ty := ⟨.point⟩

section Stages

variable (PD : PcpDecider) (ℓ : ℕ)

/-- The PCP parameters `pd`, the width `k` and `m'`, after `j` stages (`j ≥ 1`). -/
def pdD (j : ℕ) : PolyTimeFun Data Data := res (j - 1)
def kD (j : ℕ) : PolyTimeFun Data Unary := readU.comp (treeHead.comp (pdD j))
def m'D (j : ℕ) : PolyTimeFun Data Unary := readU.comp (treeHead.comp (treeTail.comp (pdD j)))

/-- The bits of the question in the input's field `i` (`2` or `4`), after `j` stages. -/
def qBits (j i : ℕ) : PolyTimeFun Data BitStr := readBits.comp (inp j i)

/-- Its oracle half. -/
def oBits (j i : ℕ) : PolyTimeFun Data BitStr :=
  leftBP.comp ((qBits j i).pair (dimProg.comp (pdD j)))

/-- Its PCP half, in runs of blocks. -/
def pBlocks (j i : ℕ) : PolyTimeFun Data Blocks :=
  blocksOfP.comp ((kD j).pair ((m'D j).pair (rightBP.comp ((qBits j i).pair
    (dimProg.comp (pdD j))))))

/-- Stage 1's argument: `((λ, μ, σ), n)`. -/
def argPar (j : ℕ) : PolyTimeFun Data Data := ap₂ treePair (lmsD j) (inp j 0)

/-- A marginal call's argument, after `j` stages: the input sampler's program and the query
`(n, marginal w (ℓ + 1) z)` at the oracle half `z` of the question in field `i`. -/
def argMarg (j i : ℕ) (w : Player) : PolyTimeFun Data Data :=
  ap₂ treePair (spD j) (ap₂ treePair (inp j 0) (encoded.comp ((const (1 : ℕ)).pair
    ((const w).pair ((const (ℓ + 1)).pair ((oBits j i).pair (const ([] : BitStr))))))))

/-- The answer blocks of the answer in field `ia`, parsed at the type in field `it`. -/
def aBlocks (j it ia : ℕ) : PolyTimeFun Data (List BitStr) :=
  let m := fst.comp (snd.comp ((SAT.ArrayProg.getD default).comp ((const 0).pair
    ((map readDesc).comp (rawListP.comp (treeTail.comp (treeTail.comp (pdD j))))))))
  snd.comp (parseBP.comp ((kD j).pair ((cntP.comp ((m.pair (m'D j)).pair
    (snd.comp ((readFinite : PolyTimeFun Data ArTy).comp (inp j it))))).pair
    (readBits.comp (if ia = 5 then inp j ia else inpLast j)))))

/-- A game check's argument, after `j` stages (`j = 6, 7`): the PCP verifier's input on the
question in field `i`, the answer in field `ia` and the marginals `rA`, `rB` stages back. -/
def argVer (j i it ia rA rB : ℕ) : PolyTimeFun Data Data :=
  let qt := res (j - 2)
  let nat (f : PolyTimeFun Data Data) := encoded.comp (readNat.comp f)
  let bits (f : PolyTimeFun Data Data) := encoded.comp (readBits.comp f)
  ap₂ treePair (ap₂ treePair
      (ap₂ treePair (dpD j) (ap₂ treePair (nat (inp j 0)) (ap₂ treePair (nat (treeTail.comp qt))
        (ap₂ treePair (nat (treeHead.comp qt)) (nat (treeTail.comp (treeTail.comp (lmsD j))))))))
      (ap₂ treePair (bits (res rA)) (bits (res rB))))
    (ap₂ treePair (encoded.comp (fst.comp (pBlocks j i))) (encoded.comp (aBlocks j it ia)))

/-- The verdict's reader, after the eight stages. -/
def readV : PolyTimeFun Data VerdictIn :=
  let descs := (map readDesc).comp (rawListP.comp (treeTail.comp (treeTail.comp (pdD 8))))
  ((kD 8).pair ((m'D 8).pair descs)).pair
    (((rawTruthProg.comp (res 1)).pair (rawTruthProg.comp (res 0))).pair
      ((((readFinite : PolyTimeFun Data ArTy).comp (inp 8 1)).pair
        ((readFinite : PolyTimeFun Data ArTy).comp (inp 8 3))).pair
        (((pBlocks 8 2).pair (pBlocks 8 4)).pair
          ((readBits.comp (inp 8 5)).pair (readBits.comp (inpLast 8))))))

/-- **The core of the answer-reduced decider**, on `((S̄, D̄, λ, μ, σ), (n, u, x, v, y, a, b))`. -/
def core : Prog :=
  seqProg (stg (argPar 0) (ParRoutine.core PD)) <|
  seqProg (stg (argPar 1) budCore) <|
  seqProg (stg (argMarg ℓ 2 2 .alice) selfUniversal.univ) <|
  seqProg (stg (argMarg ℓ 3 2 .bob) selfUniversal.univ) <|
  seqProg (stg (argMarg ℓ 4 4 .alice) selfUniversal.univ) <|
  seqProg (stg (argMarg ℓ 5 4 .bob) selfUniversal.univ) <|
  seqProg (stg (argVer 6 2 1 5 3 2) PD.verify.code) <|
  seqProg (stg (argVer 7 4 3 6 2 1) PD.verify.code) (verdictP.comp readV).code

theorem core_closed : (core PD ℓ).WellScoped 1 := by
  have hu := selfUniversal.closed
  have hv := PD.verify.closed
  exact seqProg_closed (stg_closed _ (ParRoutine.core_closed PD)) <|
    seqProg_closed (stg_closed _ budCore_closed) <|
    seqProg_closed (stg_closed _ hu) <| seqProg_closed (stg_closed _ hu) <|
    seqProg_closed (stg_closed _ hu) <| seqProg_closed (stg_closed _ hu) <|
    seqProg_closed (stg_closed _ hv) <| seqProg_closed (stg_closed _ hv) (PolyTimeFun.closed _)

end Stages

/-! ## The run -/

section Run

variable (PD : PcpDecider) (ℓ : ℕ) (sp dp : Prog) (lam mu sigma n : ℕ) (u v : ArTy)
  (x y a b : BitStr)

/-- The core's input. -/
def ctx0 : Data := .cons (encode (sp, dp, lam, mu, sigma)) (encode (n, u, x, v, y, a, b))

/-- The width of the PCP half at index `n`. -/
abbrev dB : Unary := unary (pcpDim (arPar PD lam mu sigma n) * (arPar PD lam mu sigma n).k)

/-- A marginal query at the oracle half of `z`. -/
def margQ (w : Player) (z : BitStr) : Data :=
  .cons (encode sp) (encode (n, Sampler.Query.marginal w (ℓ + 1)
    (leftBP (z, dB PD lam mu sigma n))))

variable (rxA rxB ryA ryB : Data)

/-- The PCP half of a question, in runs of blocks. -/
def pBl (z : BitStr) : Blocks :=
  blocksOf (unary (arPar PD lam mu sigma n).k) (unary (arPar PD lam mu sigma n).m')
    (rightBP (z, dB PD lam mu sigma n))

/-- The parse of an answer into blocks, at a type. -/
def aBl (t : ArTy) (s : BitStr) : List BitStr :=
  (parseBP (unary (arPar PD lam mu sigma n).k, unary (cntB (arPar PD lam mu sigma n).m
    (arPar PD lam mu sigma n).m' t.2), s)).2

/-- A game check's verdict. -/
def chkV (rA rB : Data) (z : BitStr) (t : ArTy) (s : BitStr) : Bool :=
  PD.verify (pcpInput dp n (tPcp lam mu n) (arQ lam mu n) sigma
    (readBits rA) (readBits rB) (pBl PD lam mu sigma n z).1 (aBl PD lam mu sigma n t s))

/-- The contexts after each stage. -/
def ctx1 : Data := .cons ((family PD lam mu sigma).pd n) (ctx0 sp dp lam mu sigma n u v x y a b)
def ctx2 : Data := .cons (encode (arQ lam mu n, tPcp lam mu n))
  (ctx1 PD sp dp lam mu sigma n u v x y a b)
def ctx6 : Data := .cons ryB (.cons ryA (.cons rxB (.cons rxA
  (ctx2 PD sp dp lam mu sigma n u v x y a b))))
def ctx7 : Data := .cons (encode (chkV PD dp lam mu sigma n rxA rxB x u a))
  (ctx6 PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB)
def ctx8 : Data := .cons (encode (chkV PD dp lam mu sigma n ryA ryB y v b))
  (ctx7 PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB)

end Run

/-! ## The typed decider and its acceptance law -/

section Law

variable (PD : PcpDecider) {ℓ : ℕ} (V : Verifier (ℓ + 1)) (lam mu sigma : ℕ)

/-- **The typed answer-reduced decider** of `V` at the parameters `(λ, μ, σ)`. -/
def typedDecider : CL.Detyping.TypedDecider ArTy where
  prog := hardcode (core PD ℓ) (encode (V.sampler.prog, V.decider.prog, lam, mu, sigma))
  closed := hardcode_wellScoped (core_closed PD ℓ) _

variable (n : ℕ)

/-- The game check of the typed game at index `n`. -/
abbrev chk : (Fin (V.sampler.dim n) → 𝔽₂) → (Fin (((family PD lam mu sigma)).par n).m' → Fq (((family PD lam mu sigma)).par n) (((family PD lam mu sigma)).hk n)) →
    (Fin ((((family PD lam mu sigma)).par n).m' + 6) → Fq (((family PD lam mu sigma)).par n) (((family PD lam mu sigma)).hk n)) → Bool :=
  gameCheck V n (((family PD lam mu sigma)).par n) (((family PD lam mu sigma)).hk n) PD V.decider.prog (tPcp lam mu n)
    (arQ lam mu n) sigma

/-! ## Totality -/

end Law

end MIPRE.AnswerReduction


