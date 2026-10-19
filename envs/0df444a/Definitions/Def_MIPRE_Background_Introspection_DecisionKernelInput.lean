-- Prove2me | Definitions.Def_MIPRE_Background_Introspection_DecisionKernelInput
-- name    : MIPRE_Background_Introspection_DecisionKernelInput
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T07:05:20.399427+00:00
-- url     : https://prove2.me/theorems/6c7497cb-e2d2-4f91-b905-ba373e647f3a
-- title:
--   Definitions of DecisionKernelInput: Canonical raw input parsing for the introspection decision kernel Only the fixed finite question labels are decoded by…
-- statement:
--   The definitions of the module `MIPRE.Background.Introspection.DecisionKernelInput` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Canonical raw input parsing for the introspection decision kernel. Only the fixed finite question labels are decoded by a lookup table. The source programs arrive as typed compiler metadata, never through a claimed polynomial-time decoder for arbitrary program syntax.
--
--   **Definitions** (33): `MIPRE.Introspection.DecisionKernel.Fields`; `MIPRE.Introspection.DecisionKernel.Input`; `MIPRE.Introspection.DecisionKernel.Label`; `MIPRE.Introspection.DecisionKernel.budget`; `MIPRE.Introspection.DecisionKernel.canonical`; `MIPRE.Introspection.DecisionKernel.indexField`; `MIPRE.Introspection.DecisionKernel.labelDecoder`; `MIPRE.Introspection.DecisionKernel.labelKeys`; `MIPRE.Introspection.DecisionKernel.labelOption`; `MIPRE.Introspection.DecisionKernel.labelReader`; `MIPRE.Introspection.DecisionKernel.leftAnswerField`; `MIPRE.Introspection.DecisionKernel.leftBits`; `MIPRE.Introspection.DecisionKernel.leftLabelField`; `MIPRE.Introspection.DecisionKernel.leftQuestion`; `MIPRE.Introspection.DecisionKernel.leftQuestionField`; `MIPRE.Introspection.DecisionKernel.leftType`; `MIPRE.Introspection.DecisionKernel.metadata`; `MIPRE.Introspection.DecisionKernel.originalCutoff`; `MIPRE.Introspection.DecisionKernel.parameters`; `MIPRE.Introspection.DecisionKernel.raw`; `MIPRE.Introspection.DecisionKernel.readFields`; `MIPRE.Introspection.DecisionKernel.registerWidth`; `MIPRE.Introspection.DecisionKernel.resourceTail`; `MIPRE.Introspection.DecisionKernel.rightAnswerField`; `MIPRE.Introspection.DecisionKernel.rightBits`; `MIPRE.Introspection.DecisionKernel.rightLabelField`; `MIPRE.Introspection.DecisionKernel.rightQuestion`; `MIPRE.Introspection.DecisionKernel.rightQuestionField`; `MIPRE.Introspection.DecisionKernel.rightType`; `MIPRE.Introspection.DecisionKernel.sourceDecider`; and 3 more.
--
--   **Embedded lemmas** (9): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `labelReader_encode`, `leftAnswerField_encode`, `leftLabelField_encode`, `leftQuestionField_encode`, `readFields_encode`, `rightAnswerField_encode`, `rightLabelField_encode`, `rightQuestionField_encode`, `table_not_mem`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.Introspection.DecisionKernelInput` (`MIPRE/Background/Introspection/DecisionKernelInput.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 274 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/Introspection/DecisionKernelInput.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Introspection/DecisionKernelInput.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.BigOperators.Group.Finset
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
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Rotate
import Mathlib.Data.Matrix.Basic
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
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Fin.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
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
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
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
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_RegisterReindex_B
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_CL_Downsize
import Definitions.Def_MIPRE_Foundations_CL_TypedSampler
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryConstants
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPower
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryTrace
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasis
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixInverse
import Definitions.Def_MIPRE_Foundations_LowDegree_SelfDualize
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySquareRoot
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCirculant
import Definitions.Def_MIPRE_Foundations_Cost_Iterates
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCirculantProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCirculantProg_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryKernel
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryGroupAlgebra
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryGroupAlgebra_B
import Definitions.Def_MIPRE_Foundations_LowDegree_FiniteReducedComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_IdempotentSplit
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponents_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponentsProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponentsProg_B
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
import Definitions.Def_MIPRE_Foundations_SAT_FieldTrace_B
import Definitions.Def_MIPRE_Foundations_SAT_FieldCoordinates
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_Introspection_SeedSelectorProg
import Definitions.Def_MIPRE_Foundations_SAT_TraceGram
import Definitions.Def_MIPRE_Foundations_LowDegree_SelfDual
import Definitions.Def_MIPRE_Foundations_LowDegree_NormalBasis
import Definitions.Def_MIPRE_Foundations_SAT_NormalGram
import Definitions.Def_MIPRE_Foundations_SAT_FrobeniusAction
import Definitions.Def_MIPRE_Foundations_SAT_NormalElement
import Definitions.Def_MIPRE_Foundations_SAT_FrobeniusMatrix
import Definitions.Def_MIPRE_Foundations_SAT_FrobeniusActionProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryFold
import Definitions.Def_MIPRE_Foundations_SAT_NormalElementProg
import Definitions.Def_MIPRE_Foundations_SAT_NormalElementProg_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryInverse
import Definitions.Def_MIPRE_Foundations_Introspection_LineRepresentativeProg
import Definitions.Def_MIPRE_Foundations_Cost_BinaryCompare
import Definitions.Def_MIPRE_Foundations_Introspection_SeededLineProg
import Definitions.Def_MIPRE_Foundations_Cost_TreeBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgFinite
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgParse
import Definitions.Def_MIPRE_Foundations_SAT_BasisTransport
import Definitions.Def_MIPRE_Foundations_SAT_EffectiveSelfDual
import Definitions.Def_MIPRE_Foundations_SAT_EffectiveNormalBasis
import Definitions.Def_MIPRE_Foundations_Introspection_BasisProg
import Definitions.Def_MIPRE_Foundations_Introspection_BinaryBlockProg
import Definitions.Def_MIPRE_Foundations_Introspection_BinaryBlockProg_B
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Geometry
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
import Definitions.Def_MIPRE_Foundations_Cost_FiniteEncoding
import Definitions.Def_MIPRE_Foundations_Introspection_FieldPolynomialProg
import Definitions.Def_MIPRE_Foundations_Introspection_FieldLineCheckProg
import Definitions.Def_MIPRE_Foundations_Introspection_PauliStageProg
import Definitions.Def_MIPRE_Foundations_Introspection_PauliStageProg_B
import Definitions.Def_MIPRE_Foundations_Introspection_FieldQuestionProg
import Definitions.Def_MIPRE_Foundations_Cost_SizeProgram
import Definitions.Def_MIPRE_Foundations_SAT_PcpFormat
import Definitions.Def_MIPRE_Foundations_Halting_Lists_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Halting_Arith_B
import Definitions.Def_MIPRE_Foundations_Repeat_Prims
import Definitions.Def_MIPRE_Foundations_CL_Repeat
import Definitions.Def_MIPRE_Foundations_Repeat_Bits
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Pipeline_Budget
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgSampler
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCost
import Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderRoute
import Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderProg
import Definitions.Def_MIPRE_Foundations_CL_DetypingClock
import Definitions.Def_MIPRE_Foundations_Pipeline_Introspection
import Definitions.Def_MIPRE_Foundations_Halting_PolyBounded
import Definitions.Def_MIPRE_Foundations_Introspection_ClockArithmetic
import Definitions.Def_MIPRE_Foundations_Introspection_ParserBits
import Definitions.Def_MIPRE_Foundations_Introspection_ParserAnswers
import Definitions.Def_MIPRE_Foundations_Introspection_DynamicParserSlice
import Definitions.Def_MIPRE_Foundations_Introspection_DynamicParser
import Definitions.Def_MIPRE_Foundations_Introspection_SourceCompilerParams
import Definitions.Def_MIPRE_Foundations_Introspection_PauliSamplerParams
import Definitions.Def_MIPRE_Foundations_Introspection_Clock
import Definitions.Def_MIPRE_Foundations_Introspection_ClockCost
import Definitions.Def_MIPRE_Foundations_Introspection_ClockSimulation
import Definitions.Def_MIPRE_Foundations_Introspection_ClockCompiler
import Definitions.Def_MIPRE_Foundations_Introspection_ClockSimulationCost
import Definitions.Def_MIPRE_Foundations_Introspection_SourceCompilerParamsCost
import Definitions.Def_MIPRE_Foundations_Introspection_PauliSamplerParamsCost
import Definitions.Def_MIPRE_Foundations_Introspection_SourceCompilerGuard
import Definitions.Def_MIPRE_Foundations_Introspection_ParserGuard
import Definitions.Def_MIPRE_Foundations_Introspection_SourceCompiler
import Definitions.Def_MIPRE_Foundations_Introspection_SourceCompilerCost
import Definitions.Def_MIPRE_Foundations_Introspection_DecisionPreparation
import Definitions.Def_MIPRE_LCS_Basic
import Definitions.Def_MIPRE_LCS_Common
import Definitions.Def_MIPRE_LCS_Measurement
import Definitions.Def_MIPRE_LCS_Observable
import Definitions.Def_MIPRE_LCS_Strategy_ObservableToProjector
import Definitions.Def_MIPRE_LCS_NonlocalGame
import Definitions.Def_MIPRE_LCS_Pauli
import Definitions.Def_MIPRE_LCS_MagicSquare_Strategy
import Definitions.Def_MIPRE_LCS_MagicSquare_Game
import Definitions.Def_MIPRE_Background_QLD_Game
import Definitions.Def_MIPRE_Background_QLD_CLPresentation
import Definitions.Def_MIPRE_Background_QLD_CLBinary
import Definitions.Def_MIPRE_Background_QLD_CLExplicitSeed
import Definitions.Def_MIPRE_Background_QLD_PauliStagePrograms
import Definitions.Def_MIPRE_Background_QLD_TypeEncoding
import Definitions.Def_MIPRE_Foundations_Introspection_FieldAnswerParserProg
import Definitions.Def_MIPRE_Background_QLD_PauliAnswerPrograms
import Definitions.Def_MIPRE_Foundations_Introspection_FieldIndicatorProg
import Definitions.Def_MIPRE_Foundations_Introspection_FieldTableProg
import Definitions.Def_MIPRE_Background_QLD_PauliAnswerCoding
import Definitions.Def_MIPRE_Background_QLD_PauliBranchPrograms
import Definitions.Def_MIPRE_Foundations_Introspection_FieldGammaProg
import Definitions.Def_MIPRE_Background_QLD_PauliArithmeticPrograms
import Definitions.Def_MIPRE_Background_QLD_PauliBooleanPrograms
import Definitions.Def_MIPRE_Background_QLD_BinaryBlocks
import Definitions.Def_MIPRE_Foundations_Introspection_PauliRowsProg
import Definitions.Def_MIPRE_Background_QLD_PauliBinaryPrograms
import Definitions.Def_MIPRE_Background_QLD_PauliBooleanCorrect
import Definitions.Def_MIPRE_Background_QLD_PauliBooleanSymmetry
import Definitions.Def_MIPRE_Background_QLD_PauliBooleanDispatch
import Definitions.Def_MIPRE_Background_QLD_PauliAnswerRoundtrip
import Definitions.Def_MIPRE_Foundations_WeylEPR
import Definitions.Def_MIPRE_Foundations_WeylBinary
import Definitions.Def_MIPRE_Background_QLD_PauliFullAnswerPrograms
import Definitions.Def_MIPRE_Background_QLD_PauliFullAnswerCorrect
import Definitions.Def_MIPRE_Background_QLD_PauliBinaryInterface
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
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryReadProgram
import Theorems.Thm_MIPRE_CL_Detyping_Program_readBits_encode
import Theorems.Thm_MIPRE_CL_Detyping_Program_readNat_encode

/-! # Canonical raw input parsing for the introspection decision kernel

Only the fixed finite question labels are decoded by a lookup table. The
source programs arrive as typed compiler metadata, never through a claimed
polynomial-time decoder for arbitrary program syntax.
-/

noncomputable section
namespace MIPRE.Introspection.DecisionKernel
open Cost Cost.PolyTimeFun CL.Detyping.Program AuxiliaryProgram

abbrev Label := QuestionType QLD.Ty 7
abbrev Fields := ℕ × Label × BitStr × Label × BitStr × BitStr × BitStr
abbrev Input := DecisionPreparation.KernelInput

def labelKeys : List Data := (Finset.univ.image (encode : Label → Data)).toList
def labelOption (d : Data) : Option Label := if d ∈ labelKeys then decode d else none

theorem table_not_mem (f : Data → Data) (xs : List Data) (d : Data)
    (h : d ∉ xs) : finiteTable f xs d = .nil := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.mem_cons, not_or] at h
    simp only [finiteTable, PolyTimeFun.ite_apply, ap₂_apply, treeEq_apply, id_apply, const_apply,
      h.1, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact ih h.2

def labelDecoder : PolyTimeFun Data (Option Label) := by
  let table := finiteTable (fun d => encode (labelOption d)) labelKeys
  exact {
    toFun := labelOption
    code := table.code
    closed := table.closed
    timeBound := table.timeBound
    computes := fun d => by
      obtain ⟨t, ht, hr⟩ := table.computes d
      have he : table d = encode (labelOption d) := by
        by_cases h : d ∈ labelKeys
        · exact finiteTable_apply_of_mem _ _ _ h
        · rw [table_not_mem _ _ _ h]
          simp only [labelOption, if_neg h]
          rfl
      rw [he] at hr
      exact ⟨t, ht, hr⟩ }

def labelReader : PolyTimeFun Data Label :=
  (finiteFunction (fun t : Option Label => t.getD (.inl (.pauli .X)))).comp labelDecoder

@[simp] theorem labelReader_encode (t : Label) : labelReader (encode t) = t := by
  have ht : encode t ∈ labelKeys := by simp [labelKeys]
  simp [labelReader, labelDecoder, labelOption, ht, SizedEncoding.decode_encode]

def tailN : ℕ → PolyTimeFun Data Data
  | 0 => PolyTimeFun.id Data
  | n + 1 => treeTail.comp (tailN n)

def indexField : PolyTimeFun Data ℕ := readNat.comp treeHead
def leftLabelField : PolyTimeFun Data Label := labelReader.comp (treeHead.comp (tailN 1))
def leftQuestionField : PolyTimeFun Data BitStr := readBits.comp (treeHead.comp (tailN 2))
def rightLabelField : PolyTimeFun Data Label := labelReader.comp (treeHead.comp (tailN 3))
def rightQuestionField : PolyTimeFun Data BitStr := readBits.comp (treeHead.comp (tailN 4))
def leftAnswerField : PolyTimeFun Data BitStr := readBits.comp (treeHead.comp (tailN 5))
def rightAnswerField : PolyTimeFun Data BitStr := readBits.comp (tailN 6)

def readFields : PolyTimeFun Data Fields :=
  indexField.pair (leftLabelField.pair (leftQuestionField.pair
    (rightLabelField.pair (rightQuestionField.pair (leftAnswerField.pair rightAnswerField)))))

@[simp] theorem readFields_encode (n : ℕ) (T U : Label) (x y a b : BitStr) :
    readFields (encode (n,T,x,U,y,a,b)) = (n,T,x,U,y,a,b) := by
  simp [readFields, indexField, leftLabelField, leftQuestionField, rightLabelField,
    rightQuestionField, leftAnswerField, rightAnswerField, tailN,
    encode_prod, readBits_encode, readNat_encode]

@[simp] theorem leftLabelField_encode (n : ℕ) (T U : Label) (x y a b : BitStr) :
    leftLabelField (encode (n,T,x,U,y,a,b)) = T :=
  congrArg (fun z : Fields => z.2.1) (readFields_encode n T U x y a b)

@[simp] theorem leftQuestionField_encode (n : ℕ) (T U : Label) (x y a b : BitStr) :
    leftQuestionField (encode (n,T,x,U,y,a,b)) = x :=
  congrArg (fun z : Fields => z.2.2.1) (readFields_encode n T U x y a b)

@[simp] theorem rightLabelField_encode (n : ℕ) (T U : Label) (x y a b : BitStr) :
    rightLabelField (encode (n,T,x,U,y,a,b)) = U :=
  congrArg (fun z : Fields => z.2.2.2.1) (readFields_encode n T U x y a b)

@[simp] theorem rightQuestionField_encode (n : ℕ) (T U : Label) (x y a b : BitStr) :
    rightQuestionField (encode (n,T,x,U,y,a,b)) = y :=
  congrArg (fun z : Fields => z.2.2.2.2.1) (readFields_encode n T U x y a b)

@[simp] theorem leftAnswerField_encode (n : ℕ) (T U : Label) (x y a b : BitStr) :
    leftAnswerField (encode (n,T,x,U,y,a,b)) = a :=
  congrArg (fun z : Fields => z.2.2.2.2.2.1) (readFields_encode n T U x y a b)

@[simp] theorem rightAnswerField_encode (n : ℕ) (T U : Label) (x y a b : BitStr) :
    rightAnswerField (encode (n,T,x,U,y,a,b)) = b :=
  congrArg (fun z : Fields => z.2.2.2.2.2.2) (readFields_encode n T U x y a b)

def raw : PolyTimeFun Input Data := fst
def metadata : PolyTimeFun Input DecisionPreparation.Metadata := fst.comp snd
def resourceTail : PolyTimeFun Input (Unary × ℕ × PauliSamplerParameters.Parameters × ℕ × ℕ) :=
  snd.comp snd
def budget : PolyTimeFun Input Unary := fst.comp resourceTail
def sourceIndex : PolyTimeFun Input ℕ := fst.comp (snd.comp resourceTail)
def parameters : PolyTimeFun Input PauliSamplerParameters.Parameters :=
  fst.comp (snd.comp (snd.comp resourceTail))
def registerWidth : PolyTimeFun Input ℕ := fst.comp (snd.comp (snd.comp (snd.comp resourceTail)))
def originalCutoff : PolyTimeFun Input ℕ := snd.comp (snd.comp (snd.comp (snd.comp resourceTail)))
def sourceSampler : PolyTimeFun Input Prog := fst.comp (fst.comp metadata)
def sourceDecider : PolyTimeFun Input Prog := snd.comp (fst.comp metadata)

def leftType : PolyTimeFun Input Label := leftLabelField.comp raw
def rightType : PolyTimeFun Input Label := rightLabelField.comp raw
def leftQuestion : PolyTimeFun Input BitStr := leftQuestionField.comp raw
def rightQuestion : PolyTimeFun Input BitStr := rightQuestionField.comp raw
def leftBits : PolyTimeFun Input BitStr := leftAnswerField.comp raw
def rightBits : PolyTimeFun Input BitStr := rightAnswerField.comp raw

def canonical : PolyTimeFun Input Bool := equal raw (encoded.comp (readFields.comp raw))

end MIPRE.Introspection.DecisionKernel
end


