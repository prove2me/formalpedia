-- Prove2me | Definitions.Def_MIPRE_Background_Introspection_PauliSampler
-- name    : MIPRE_Background_Introspection_PauliSampler
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T06:55:59.993698+00:00
-- url     : https://prove2.me/theorems/0dbf8fb5-152b-4c07-bd56-52b71d3b45eb
-- title:
--   Definitions of PauliSampler: The canonical index-dependent executable Pauli sampler The field, selector, basis and question dimension are the…
-- statement:
--   The definitions of the module `MIPRE.Background.Introspection.PauliSampler` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The canonical index-dependent executable Pauli sampler. The field, selector, basis and question dimension are the canonical index-dependent choices. The sampler program computes these parameters from the index and calls the uniform query router. Its semantic family uses the effective Shoup self-dual basis, and all query contracts concern the actual numbered binary vectors. This is the canonical positive-index component. The final introspection compiler must wrap the detyped sampler with a zero-dimensional fallback at zero index (and zero boundedness parameter) to respect its all-index budget.
--
--   **Definitions** (7): `MIPRE.Introspection.PauliSampler.compiler` (The compiler copies only the binary encoding of the boundedness parameter.); `MIPRE.Introspection.PauliSampler.dimension`; `MIPRE.Introspection.PauliSampler.post`; `MIPRE.Introspection.PauliSampler.presentation`; `MIPRE.Introspection.PauliSampler.prog`; `MIPRE.Introspection.PauliSampler.route` (Route the index to parameter generation and retain the complete raw query.); `MIPRE.Introspection.PauliSampler.sampler` (The actual uniform three-level Pauli sampler at canonical parameters.).
--
--   **Embedded lemmas** (8): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `presentation_exactlyOn`, `prog_closed`, `prog_halts`, `prog_runs`, `query_factor`, `query_linear`, `query_marginal`, `registerPower_neZero`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.Introspection.PauliSampler` (`MIPRE/Background/Introspection/PauliSampler.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 211 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/Introspection/PauliSampler.lean; blueprint lem:intro-canonical-sampler

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Introspection/PauliSampler.lean (definition bundle: declarations the uploaded statements rest on);
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
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
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
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
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
import Definitions.Def_MIPRE_Foundations_Introspection_PauliStageProg
import Definitions.Def_MIPRE_Foundations_Introspection_PauliStageProg_B
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
import Definitions.Def_MIPRE_Background_QLD_BinaryBlocks
import Definitions.Def_MIPRE_Foundations_Introspection_PauliRowsProg
import Definitions.Def_MIPRE_Foundations_Introspection_PauliFactorProg
import Definitions.Def_MIPRE_Background_QLD_SamplerQueryProgram
import Definitions.Def_MIPRE_Background_QLD_PauliFactorPrograms
import Theorems.Thm_MIPRE_CL_Detyping_Program_readNat_encode
import Theorems.Thm_MIPRE_Cost_Prog_routeOneCall_closed
import Theorems.Thm_MIPRE_Cost_Prog_routeOneCall_indirect
import Theorems.Thm_MIPRE_Cost_hardcode_time
import Theorems.Thm_MIPRE_Cost_hardcode_wellScoped
import Theorems.Thm_MIPRE_Introspection_PauliSamplerParameters_prog_closed
import Theorems.Thm_MIPRE_Introspection_PauliSamplerParameters_prog_runs
import Theorems.Thm_MIPRE_Introspection_PauliSamplerParameters_registerPower_eq
import Theorems.Thm_MIPRE_Introspection_PauliSamplerParameters_registerPower_pos
import Theorems.Thm_MIPRE_Introspection_PauliSamplerParameters_selectorBits_le_fieldBits
import Theorems.Thm_MIPRE_QLD_PauliCL_ExplicitSeed_binaryPresentation_exactlyOn
import Theorems.Thm_MIPRE_QLD_PauliCL_SamplerProgram_query_dimension
import Theorems.Thm_MIPRE_QLD_PauliCL_SamplerProgram_query_factor
import Theorems.Thm_MIPRE_QLD_PauliCL_SamplerProgram_query_linear
import Theorems.Thm_MIPRE_QLD_PauliCL_SamplerProgram_query_marginal
import Theorems.Thm_MIPRE_QLD_PauliCL_factorBits_correct
import Theorems.Thm_MIPRE_QLD_PauliCL_linearBits_correct
import Theorems.Thm_MIPRE_QLD_PauliCL_marginalBits_correct

/-! # The canonical index-dependent executable Pauli sampler

The field, selector, basis and question dimension are the canonical
index-dependent choices. The sampler program computes these parameters from
the index and calls the uniform query router. Its semantic family uses the
effective Shoup self-dual basis, and all query contracts concern the actual
numbered binary vectors.

This is the canonical positive-index component. The final introspection
compiler must wrap the detyped sampler with a zero-dimensional fallback at
zero index (and zero boundedness parameter) to respect its all-index budget.
-/

noncomputable section
namespace MIPRE.Introspection.PauliSampler
open Cost Cost.Prog Cost.PolyTimeFun CL CL.Detyping.Program SAT
open SourceCompiler PauliSamplerParameters QLD QLD.PauliCL

local instance registerPower_neZero (c lam n : ℕ) : NeZero (registerPower c lam n) :=
  ⟨by have := registerPower_pos c lam n; omega⟩

def dimension (c lam n : ℕ) : ℕ :=
  (3 * registerPower c lam n + 3) * fieldBits c lam n

def presentation (c : ℕ) (hc : 1 ≤ c) (he : Even c) (lam n : ℕ) (T : Ty) :
    CLFun 𝔽₂ (Fin (dimension c lam n)) 3 :=
  ExplicitSeed.binaryPresentation
    (SeedProgram.selector (shoupBinField (fieldBits c lam n) (fieldBits_pos c lam n))
      (selectorBits c lam n) (selectorBits_le_fieldBits hc lam n))
    (shoupSelfDualNormalBasis (fieldBits c lam n) (fieldBits_pos c lam n)
      (fieldBits_odd he lam n)) T

theorem presentation_exactlyOn (c : ℕ) (hc : 1 ≤ c) (he : Even c)
    (lam n : ℕ) (T : Ty) : (presentation c hc he lam n T).ExactlyOn Finset.univ :=
  ExplicitSeed.binaryPresentation_exactlyOn _ _ _

/-- Route the index to parameter generation and retain the complete raw query. -/
def route : PolyTimeFun Data (Bool × Data) :=
  (const true).pair (ap₂ treePair (encoded.comp (readNat.comp treeHead)) treeTail)

def post : PolyTimeFun (Data × Data) Data := ap₂ treePair snd fst

def prog (c lam : ℕ) : Prog :=
  .let_ (routeOneCall route (hardcode (PauliSamplerParameters.prog c) (encode lam)) post)
    QLD.PauliCL.SamplerProgram.query.code

theorem prog_closed (c lam : ℕ) : (prog c lam).WellScoped 1 :=
  ⟨routeOneCall_closed route (hardcode_wellScoped (PauliSamplerParameters.prog_closed c) _) post,
    QLD.PauliCL.SamplerProgram.query.closed.mono (by omega) _⟩

theorem prog_runs (c lam n : ℕ) (d : Data) : ∃ time,
    (prog c lam).Runs (.cons (encode n) d)
      (QLD.PauliCL.SamplerProgram.query (parameters c lam n, d)) time := by
  obtain ⟨t₁, h₁⟩ := PauliSamplerParameters.prog_runs c lam n
  have h₂ := hardcode_time (PauliSamplerParameters.prog_closed c) h₁
  obtain ⟨t₃, h₃⟩ := routeOneCall_indirect route
    (hardcode_wellScoped (PauliSamplerParameters.prog_closed c) _) post
    (.cons (encode n) d) (encode n) d (encode (parameters c lam n)) _
    (by simp [route, readNat_encode]) h₂
  have hout : post (d, encode (parameters c lam n)) =
      encode (parameters c lam n, d) := rfl
  rw [hout] at h₃
  obtain ⟨t₄, _, h₄⟩ := QLD.PauliCL.SamplerProgram.query.computes (parameters c lam n, d)
  exact ⟨_, Eval.let_ h₃
    (Eval.append_of_wellScoped h₄ QLD.PauliCL.SamplerProgram.query.closed _)⟩

theorem prog_halts (c lam n : ℕ) (d : Data) :
    Halts (prog c lam) (.cons (encode n) d) := by
  obtain ⟨t, ht⟩ := prog_runs c lam n d
  exact ⟨_, t, ht⟩

set_option backward.isDefEq.respectTransparency false in
theorem query_marginal (c : ℕ) (hc : 1 ≤ c) (he : Even c)
    (lam n : ℕ) (w : Player) (T : Ty) (r : ℕ) (z : BitStr)
    (hr1 : 1 ≤ r) (hr3 : r ≤ 3) (hz : z.length = dimension c lam n) :
    QLD.PauliCL.SamplerProgram.query
      (parameters c lam n, encode (TypedSampler.Query.atType T (.marginal w r z))) =
      encode (toBits (((presentation c hc he lam n T).truncate r).eval
        (ofBits (dimension c lam n) z))) := by
  rw [QLD.PauliCL.SamplerProgram.query_marginal]
  let b := shoupSelfDualNormalBasis (fieldBits c lam n) (fieldBits_pos c lam n)
    (fieldBits_odd he lam n)
  let x := (binaryVectorEquiv (m := 2 ^ selectorBits c lam n) b).symm
    (ofBits (dimension c lam n) z)
  have hx : toBits (binaryVectorEquiv b x) = z := by
    exact (congrArg CL.toBits ((binaryVectorEquiv b).apply_symm_apply _)).trans (toBits_ofBits hz)
  have hxe : binaryVectorEquiv b x = ofBits (dimension c lam n) z :=
    (binaryVectorEquiv b).apply_symm_apply _
  have h := marginalBits_correct (fieldBits c lam n) (fieldBits_pos c lam n)
    (fieldBits_odd he lam n) (selectorBits c lam n)
    (selectorBits_le_fieldBits hc lam n) T r hr1 hr3 x x
  dsimp only [b] at hx hxe
  rw [hx, hxe] at h
  apply congrArg encode
  simpa only [parameters, presentation, registerPower_eq] using h

set_option backward.isDefEq.respectTransparency false in
theorem query_linear (c : ℕ) (hc : 1 ≤ c) (he : Even c)
    (lam n : ℕ) (w : Player) (T : Ty) (r : ℕ) (u y : BitStr)
    (hr1 : 1 ≤ r) (hr3 : r ≤ 3)
    (hu : u.length = dimension c lam n) (hy : y.length = dimension c lam n) :
    QLD.PauliCL.SamplerProgram.query
      (parameters c lam n, encode (TypedSampler.Query.atType T (.linear w r u y))) =
      encode (toBits ((presentation c hc he lam n T).mapOfPrefix (r - 1)
        (ofBits (dimension c lam n) u) (ofBits (dimension c lam n) y))) := by
  rw [QLD.PauliCL.SamplerProgram.query_linear]
  let b := shoupSelfDualNormalBasis (fieldBits c lam n) (fieldBits_pos c lam n)
    (fieldBits_odd he lam n)
  let v := (binaryVectorEquiv (m := 2 ^ selectorBits c lam n) b).symm
    (ofBits (dimension c lam n) u)
  let x := (binaryVectorEquiv (m := 2 ^ selectorBits c lam n) b).symm
    (ofBits (dimension c lam n) y)
  have hv : toBits (binaryVectorEquiv b v) = u := by
    exact (congrArg CL.toBits ((binaryVectorEquiv b).apply_symm_apply _)).trans (toBits_ofBits hu)
  have hx : toBits (binaryVectorEquiv b x) = y := by
    exact (congrArg CL.toBits ((binaryVectorEquiv b).apply_symm_apply _)).trans (toBits_ofBits hy)
  have hve : binaryVectorEquiv b v = ofBits (dimension c lam n) u :=
    (binaryVectorEquiv b).apply_symm_apply _
  have hxe : binaryVectorEquiv b x = ofBits (dimension c lam n) y :=
    (binaryVectorEquiv b).apply_symm_apply _
  have h := linearBits_correct (fieldBits c lam n) (fieldBits_pos c lam n)
    (fieldBits_odd he lam n) (selectorBits c lam n)
    (selectorBits_le_fieldBits hc lam n) T r hr1 hr3 v x
  dsimp only [b] at hv hx hve hxe
  rw [hv, hx, hve, hxe] at h
  apply congrArg encode
  convert h using 1 <;> rfl

theorem query_factor (c : ℕ) (hc : 1 ≤ c) (he : Even c)
    (lam n : ℕ) (w : Player) (T : Ty) (r : ℕ) (u : BitStr)
    (hr1 : 1 ≤ r) (hr3 : r ≤ 3) :
    QLD.PauliCL.SamplerProgram.query
      (parameters c lam n, encode (TypedSampler.Query.atType T (.factor w r u))) =
      encode (indicatorBits ((presentation c hc he lam n T).factorOfPrefix (r - 1)
        (ofBits (dimension c lam n) u))) := by
  rw [QLD.PauliCL.SamplerProgram.query_factor]
  apply congrArg encode
  exact factorBits_correct _ _ T (selectorBits c lam n) r hr1 hr3 _

/-- The actual uniform three-level Pauli sampler at canonical parameters. -/
def sampler (c : ℕ) (hc : 1 ≤ c) (he : Even c) (lam : ℕ) : TypedSampler 3 Ty where
  prog := prog c lam
  closed := prog_closed c lam
  dim := dimension c lam
  cl n _ := presentation c hc he lam n
  cl_exactlyOn n _ := presentation_exactlyOn c hc he lam n
  runs_dimension n := by
    obtain ⟨time, ht⟩ := prog_runs c lam n (encode (TypedSampler.Query.dimension : TypedSampler.Query Ty))
    rw [QLD.PauliCL.SamplerProgram.query_dimension] at ht
    exact ⟨time, by simpa only [parameters, length_unary, dimension, encode_prod] using ht⟩
  runs_marginal n w T r z hr1 hr3 hz := by
    obtain ⟨time, ht⟩ := prog_runs c lam n
      (encode (TypedSampler.Query.atType T (.marginal w r z)))
    exact ⟨time, by rw [query_marginal c hc he lam n w T r z hr1 hr3 hz] at ht; exact ht⟩
  runs_linear n w T r u y hr1 hr3 hu hy := by
    have huLen : u.length = dimension c lam n := by
      obtain ⟨x, rfl⟩ := hu
      exact length_toBits _
    obtain ⟨time, ht⟩ := prog_runs c lam n
      (encode (TypedSampler.Query.atType T (.linear w r u y)))
    exact ⟨time, by rw [query_linear c hc he lam n w T r u y hr1 hr3 huLen hy] at ht; exact ht⟩
  runs_factor n w T r u hr1 hr3 _ := by
    obtain ⟨time, ht⟩ := prog_runs c lam n
      (encode (TypedSampler.Query.atType T (.factor w r u)))
    exact ⟨time, by rw [query_factor c hc he lam n w T r u hr1 hr3] at ht; exact ht⟩
  halts := prog_halts c lam

/-- The compiler copies only the binary encoding of the boundedness parameter. -/
def compiler (c : ℕ) : PolyTimeFun ℕ Prog :=
  ClockSimulation.codeLet.comp
    (((ClockSimulation.codeRoute route post).comp
      ((PolyTimeFun.smn ℕ).comp ((const (PauliSamplerParameters.prog c)).pair (PolyTimeFun.id ℕ)))).pair
        (const QLD.PauliCL.SamplerProgram.query.code))

end MIPRE.Introspection.PauliSampler
end


