-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_CanonicalPrimal
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_CanonicalPrimal
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T03:17:46.660471+00:00
-- url     : https://prove2.me/theorems/05e7e66b-223d-4790-b18c-4b2d2424c8e1
-- title:
--   Definitions of CanonicalPrimal: Section 9 — Canonical matrix SDP primal block form This module contains the canonical block Hilbert space,…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.SelfImprovement.MatrixRealization.CanonicalPrimal` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Section 9 — Canonical matrix SDP primal block form. This module contains the canonical block Hilbert space, diagonal-block operators, primal slack block, and extraction of paper primal submeasurements from feasible canonical primal matrices.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Definitions** (14): `MIPStarRE.LDT.SelfImprovement.MatrixSdpCanonicalBlockIndex` (The block index set for the canonical primal SDP.); `MIPStarRE.LDT.SelfImprovement.MatrixSdpCanonicalPrimalFeasible` (Feasibility for the canonical primal block SDP: the block variable is positive semidefinite and satisfies the equality constraint…); `MIPStarRE.LDT.SelfImprovement.matrixSdpCanonicalBlockDiagonal` (The block-diagonal matrix with prescribed diagonal blocks.); `MIPStarRE.LDT.SelfImprovement.matrixSdpCanonicalBlockDiagonalLinearMap` (The linear map underlying the canonical block-diagonal construction.); `MIPStarRE.LDT.SelfImprovement.matrixSdpCanonicalBlockDiagonalRingHom` (The ring homomorphism underlying the canonical block-diagonal construction.); `MIPStarRE.LDT.SelfImprovement.matrixSdpCanonicalBlockHilbertSpace` (The finite Hilbert space carrying the canonical block primal variable.); `MIPStarRE.LDT.SelfImprovement.matrixSdpCanonicalConstraintOperator` (The operator-valued canonical equality constraint `∑_b X_{bb} = I`.); `MIPStarRE.LDT.SelfImprovement.matrixSdpCanonicalConstraintOperatorLinearMap` (The canonical equality-constraint operator as a complex-linear map.); `MIPStarRE.LDT.SelfImprovement.matrixSdpCanonicalDiagonalBlock` (The diagonal block of a canonical primal matrix.); `MIPStarRE.LDT.SelfImprovement.matrixSdpCanonicalDiagonalBlockLinearMap` (Projection onto one diagonal block of a canonical primal matrix, as a complex-linear map in the ambient block matrix.); and 3 more.
--
--   **Embedded lemmas** (30): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `matrixSdpCanonicalBlockDiagonalLinearMap_apply`, `matrixSdpCanonicalBlockDiagonal_add`, `matrixSdpCanonicalBlockDiagonal_apply`, `matrixSdpCanonicalBlockDiagonal_eq_reindex_blockDiagonal`, `matrixSdpCanonicalBlockDiagonal_neg`, `matrixSdpCanonicalBlockDiagonal_one`, `matrixSdpCanonicalBlockDiagonal_smul`, `matrixSdpCanonicalBlockDiagonal_sub`, `matrixSdpCanonicalBlockDiagonal_zero`, `matrixSdpCanonicalConstraintOperatorLinearMap_apply`, ….
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.SelfImprovement.MatrixRealization.CanonicalPrimal` (`MIPRE/Background/LIDT/MIPStarRE/LDT/SelfImprovement/MatrixRealization/CanonicalPrimal.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 43 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/SelfImprovement/MatrixRealization/CanonicalPrimal.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/SelfImprovement/MatrixRealization/CanonicalPrimal.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/SelfImprovement/MatrixRealization/CanonicalPrimal.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.NonUnitalHom
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharP.Invertible
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.IsField
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.Group.Invertible.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.Group.Subsemigroup.Defs
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.Algebra.GroupWithZero.Invertible
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Notation.Pi.Basic
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Opposites
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.IsBotOne
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Nonneg.Basic
import Mathlib.Algebra.Order.Nonneg.Module
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Sub.Defs
import Mathlib.Algebra.Order.SuccPred
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Ring.CompTypeclasses
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Ring.Pi
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Unitary
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.CStarAlgebra.Module.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Real.Spectrum
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Countable.Defs
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finset.Attach
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Erase
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.OfMap
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sort
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Multiset.Bind
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Multiset.Defs
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.Multiset.ZeroCons
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.NNReal.Star
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Prod.Basic
import Mathlib.Data.Rat.Init
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Operations
import Mathlib.Data.SetLike.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.Separable
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.CharP
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Basic
import Mathlib.Logic.Embedding.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Function.Defs
import Mathlib.Logic.IsEmpty.Basic
import Mathlib.Logic.IsEmpty.Defs
import Mathlib.Logic.Nonempty
import Mathlib.Logic.Nontrivial.Defs
import Mathlib.Logic.Unique
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Hom.Basic
import Mathlib.Order.Lattice
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.MinMax
import Mathlib.Order.Monotone.Defs
import Mathlib.Order.Nat
import Mathlib.Order.Notation
import Mathlib.Order.RelClasses
import Mathlib.Order.SetNotation
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Algebra.Star.Real
import Mathlib.Topology.Bases
import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Continuous
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.EMetricSpace.Defs
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.Real
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.UniformSpace.Defs
import Mathlib.Topology.UniformSpace.Real
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MainInductionStep_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Statements
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_MeasurementLift
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_ConsistencyBridges
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Projectivization
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Operators
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Families
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Fourier
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_MatrixRealization_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_MatrixRealization_TraceForms
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Base

set_option backward.isDefEq.respectTransparency false

/-!
# Section 9 — Canonical matrix SDP primal block form

This module contains the canonical block Hilbert space, diagonal-block
operators, primal slack block, and extraction of paper primal submeasurements
from feasible canonical primal matrices.

## References

- `references/ldt-paper/self_improvement.tex`
-/

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

/-- The block index set for the canonical primal SDP.

The `some g` blocks carry the primal operators `T_g`.  The `none` block is the
slack block `S` in the canonical equality constraint
`∑_g T_g + S = I`. -/
abbrev MatrixSdpCanonicalBlockIndex (params : Parameters) [FieldModel params.q] :=
  Option (Polynomial params)

/-- The finite Hilbert space carrying the canonical block primal variable. -/
noncomputable def matrixSdpCanonicalBlockHilbertSpace (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) : FiniteHilbertSpace where
  carrier := MatrixSdpCanonicalBlockIndex params × model.space.carrier
  instFintype := inferInstance
  instDecidableEq := inferInstance
  instNonempty := inferInstance

/-- The diagonal block of a canonical primal matrix. -/
def matrixSdpCanonicalDiagonalBlock (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (b : MatrixSdpCanonicalBlockIndex params) : MatrixOperator model.space :=
  fun i j => X (b, i) (b, j)

/-- Projection onto one diagonal block of a canonical primal matrix, as a
complex-linear map in the ambient block matrix. -/
noncomputable def matrixSdpCanonicalDiagonalBlockLinearMap (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (b : MatrixSdpCanonicalBlockIndex params) :
    MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model) →ₗ[ℂ]
      MatrixOperator model.space :=
  Matrix.submatrixLinearMap ℂ
    (fun i : model.space.carrier => (b, i))
    (fun i : model.space.carrier => (b, i))

@[simp] theorem matrixSdpCanonicalDiagonalBlockLinearMap_apply (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (b : MatrixSdpCanonicalBlockIndex params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)) :
    matrixSdpCanonicalDiagonalBlockLinearMap params model b X =
      matrixSdpCanonicalDiagonalBlock params model X b :=
  rfl

/-- The diagonal-block projection sends the zero canonical matrix to zero. -/
@[simp] theorem matrixSdpCanonicalDiagonalBlock_zero (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (b : MatrixSdpCanonicalBlockIndex params) :
    matrixSdpCanonicalDiagonalBlock params model
        (0 : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)) b =
      (0 : MatrixOperator model.space) := by
  simpa only [matrixSdpCanonicalDiagonalBlockLinearMap_apply] using
    map_zero (matrixSdpCanonicalDiagonalBlockLinearMap params model b)

/-- The diagonal-block projection preserves addition. -/
@[simp] theorem matrixSdpCanonicalDiagonalBlock_add (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X Y : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (b : MatrixSdpCanonicalBlockIndex params) :
    matrixSdpCanonicalDiagonalBlock params model (X + Y) b =
      matrixSdpCanonicalDiagonalBlock params model X b +
        matrixSdpCanonicalDiagonalBlock params model Y b := by
  simpa only [matrixSdpCanonicalDiagonalBlockLinearMap_apply] using
    map_add (matrixSdpCanonicalDiagonalBlockLinearMap params model b) X Y

/-- The diagonal-block projection preserves negation. -/
@[simp] theorem matrixSdpCanonicalDiagonalBlock_neg (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (b : MatrixSdpCanonicalBlockIndex params) :
    matrixSdpCanonicalDiagonalBlock params model (-X) b =
      -matrixSdpCanonicalDiagonalBlock params model X b := by
  simpa only [matrixSdpCanonicalDiagonalBlockLinearMap_apply] using
    map_neg (matrixSdpCanonicalDiagonalBlockLinearMap params model b) X

/-- The diagonal-block projection preserves subtraction. -/
@[simp] theorem matrixSdpCanonicalDiagonalBlock_sub (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X Y : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (b : MatrixSdpCanonicalBlockIndex params) :
    matrixSdpCanonicalDiagonalBlock params model (X - Y) b =
      matrixSdpCanonicalDiagonalBlock params model X b -
        matrixSdpCanonicalDiagonalBlock params model Y b := by
  simpa only [matrixSdpCanonicalDiagonalBlockLinearMap_apply] using
    map_sub (matrixSdpCanonicalDiagonalBlockLinearMap params model b) X Y

/-- The diagonal-block projection preserves complex scalar multiplication. -/
@[simp] theorem matrixSdpCanonicalDiagonalBlock_smul (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (c : ℂ)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (b : MatrixSdpCanonicalBlockIndex params) :
    matrixSdpCanonicalDiagonalBlock params model (c • X) b =
      c • matrixSdpCanonicalDiagonalBlock params model X b := by
  simpa only [matrixSdpCanonicalDiagonalBlockLinearMap_apply] using
    map_smul (matrixSdpCanonicalDiagonalBlockLinearMap params model b) c X

/-- The ring homomorphism underlying the canonical block-diagonal construction.

The canonical SDP indexes its matrix space by `(block, vector)`, while Mathlib's
`Matrix.blockDiagonalRingHom` uses `(vector, block)`.  This map composes
Mathlib's block-diagonal ring homomorphism with the canonical reindexing
equivalence. -/
noncomputable def matrixSdpCanonicalBlockDiagonalRingHom (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    (MatrixSdpCanonicalBlockIndex params → MatrixOperator model.space) →+*
      MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model) :=
  (Matrix.reindexAlgEquiv ℂ ℂ
    (Equiv.prodComm model.space.carrier
      (MatrixSdpCanonicalBlockIndex params))).toRingEquiv.toRingHom.comp
      (Matrix.blockDiagonalRingHom model.space.carrier (MatrixSdpCanonicalBlockIndex params) ℂ)

/-- The linear map underlying the canonical block-diagonal construction.

This is the linear counterpart of `matrixSdpCanonicalBlockDiagonalRingHom`.
The construction is Mathlib's block-diagonal linear map followed by the
canonical reindexing of the SDP block space. -/
noncomputable def matrixSdpCanonicalBlockDiagonalLinearMap (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    (MatrixSdpCanonicalBlockIndex params → MatrixOperator model.space) →ₗ[ℂ]
      MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model) :=
  (Matrix.reindexLinearEquiv ℂ ℂ
    (Equiv.prodComm model.space.carrier (MatrixSdpCanonicalBlockIndex params))
    (Equiv.prodComm model.space.carrier (MatrixSdpCanonicalBlockIndex params))).toLinearMap.comp
      (Matrix.blockDiagonalLinearMap ℂ model.space.carrier model.space.carrier
        (MatrixSdpCanonicalBlockIndex params) ℂ)

/-- The operator-valued canonical equality constraint `∑_b X_{bb} = I`.

The paper states the same constraint as the scalar family
`Tr(D_{ij}^† X) = b_{ij}` for all matrix units `D_{ij}` and then identifies it
with the operator equation `∑_b X_{bb} = I`. This definition records the
left-hand operator of that equivalent equation. -/
noncomputable def matrixSdpCanonicalConstraintOperator (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)) :
    MatrixOperator model.space :=
  ∑ b : MatrixSdpCanonicalBlockIndex params,
    matrixSdpCanonicalDiagonalBlock params model X b

/-- The canonical equality-constraint operator as a complex-linear map. -/
noncomputable def matrixSdpCanonicalConstraintOperatorLinearMap (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model) →ₗ[ℂ]
      MatrixOperator model.space :=
  ∑ b : MatrixSdpCanonicalBlockIndex params,
    matrixSdpCanonicalDiagonalBlockLinearMap params model b

@[simp] theorem matrixSdpCanonicalConstraintOperatorLinearMap_apply
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)) :
    matrixSdpCanonicalConstraintOperatorLinearMap params model X =
      matrixSdpCanonicalConstraintOperator params model X := by
  simp [matrixSdpCanonicalConstraintOperatorLinearMap, matrixSdpCanonicalConstraintOperator]

/-- The canonical equality-constraint operator sends zero to zero. -/
@[simp] theorem matrixSdpCanonicalConstraintOperator_zero (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    matrixSdpCanonicalConstraintOperator params model
        (0 : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)) =
      (0 : MatrixOperator model.space) := by
  simpa only [matrixSdpCanonicalConstraintOperatorLinearMap_apply] using
    map_zero (matrixSdpCanonicalConstraintOperatorLinearMap params model)

/-- The canonical equality-constraint operator preserves addition. -/
@[simp] theorem matrixSdpCanonicalConstraintOperator_add (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X Y : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)) :
    matrixSdpCanonicalConstraintOperator params model (X + Y) =
      matrixSdpCanonicalConstraintOperator params model X +
        matrixSdpCanonicalConstraintOperator params model Y := by
  simpa only [matrixSdpCanonicalConstraintOperatorLinearMap_apply] using
    map_add (matrixSdpCanonicalConstraintOperatorLinearMap params model) X Y

/-- The canonical equality-constraint operator preserves negation. -/
@[simp] theorem matrixSdpCanonicalConstraintOperator_neg (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)) :
    matrixSdpCanonicalConstraintOperator params model (-X) =
      -matrixSdpCanonicalConstraintOperator params model X := by
  simpa only [matrixSdpCanonicalConstraintOperatorLinearMap_apply] using
    map_neg (matrixSdpCanonicalConstraintOperatorLinearMap params model) X

/-- The canonical equality-constraint operator preserves subtraction. -/
@[simp] theorem matrixSdpCanonicalConstraintOperator_sub (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X Y : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)) :
    matrixSdpCanonicalConstraintOperator params model (X - Y) =
      matrixSdpCanonicalConstraintOperator params model X -
        matrixSdpCanonicalConstraintOperator params model Y := by
  simpa only [matrixSdpCanonicalConstraintOperatorLinearMap_apply] using
    map_sub (matrixSdpCanonicalConstraintOperatorLinearMap params model) X Y

/-- The canonical equality-constraint operator preserves complex scalar
multiplication. -/
@[simp] theorem matrixSdpCanonicalConstraintOperator_smul (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (c : ℂ)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)) :
    matrixSdpCanonicalConstraintOperator params model (c • X) =
      c • matrixSdpCanonicalConstraintOperator params model X := by
  simpa only [matrixSdpCanonicalConstraintOperatorLinearMap_apply] using
    map_smul (matrixSdpCanonicalConstraintOperatorLinearMap params model) c X

/-- The block-diagonal matrix with prescribed diagonal blocks. -/
noncomputable def matrixSdpCanonicalBlockDiagonal (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (B : MatrixSdpCanonicalBlockIndex params → MatrixOperator model.space) :
    MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model) :=
  matrixSdpCanonicalBlockDiagonalRingHom params model B

@[simp]
theorem matrixSdpCanonicalBlockDiagonalLinearMap_apply (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (B : MatrixSdpCanonicalBlockIndex params → MatrixOperator model.space) :
    matrixSdpCanonicalBlockDiagonalLinearMap params model B =
      matrixSdpCanonicalBlockDiagonal params model B :=
  by
    ext x y
    try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal

/-- The canonical SDP block layout is the Mathlib block-diagonal layout after
commuting the matrix-space index with the block index. -/
theorem matrixSdpCanonicalBlockDiagonal_eq_reindex_blockDiagonal
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (B : MatrixSdpCanonicalBlockIndex params → MatrixOperator model.space) :
    matrixSdpCanonicalBlockDiagonal params model B =
      Matrix.reindex
        (Equiv.prodComm model.space.carrier (MatrixSdpCanonicalBlockIndex params))
        (Equiv.prodComm model.space.carrier (MatrixSdpCanonicalBlockIndex params))
        (Matrix.blockDiagonal B) :=
  rfl

/-- The canonical block-diagonal construction sends the zero family to the zero
operator. -/
@[simp] theorem matrixSdpCanonicalBlockDiagonal_zero
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    matrixSdpCanonicalBlockDiagonal params model
        (0 : MatrixSdpCanonicalBlockIndex params → MatrixOperator model.space) =
      (0 : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)) := by
  simpa only [matrixSdpCanonicalBlockDiagonalLinearMap_apply] using
    map_zero (matrixSdpCanonicalBlockDiagonalLinearMap params model)

/-- Entrywise form of the canonical block-diagonal matrix.

This is the old case-split presentation, now derived from Mathlib's
`Matrix.blockDiagonal` through the index reordering used by
`matrixSdpCanonicalBlockDiagonal`. -/
@[simp] theorem matrixSdpCanonicalBlockDiagonal_apply
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (B : MatrixSdpCanonicalBlockIndex params → MatrixOperator model.space)
    (b c : MatrixSdpCanonicalBlockIndex params) (i j : model.space.carrier) :
    matrixSdpCanonicalBlockDiagonal params model B (b, i) (c, j) =
      if b = c then B b i j else 0 := by
  rw [matrixSdpCanonicalBlockDiagonal_eq_reindex_blockDiagonal]
  by_cases hbc : b = c
  · subst c
    simp
  · simpa [hbc] using
      (Matrix.blockDiagonal_apply_ne B i j hbc)

/-- The canonical block diagonal with identity on every block is the identity
operator on the canonical block Hilbert space. -/
@[simp] theorem matrixSdpCanonicalBlockDiagonal_one
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    matrixSdpCanonicalBlockDiagonal params model
        (fun _ : MatrixSdpCanonicalBlockIndex params =>
          (1 : MatrixOperator model.space)) =
      (1 : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)) := by
  exact map_one (matrixSdpCanonicalBlockDiagonalRingHom params model)

/-- Addition of canonical block-diagonal operators is blockwise addition. -/
@[simp] theorem matrixSdpCanonicalBlockDiagonal_add
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (B D : MatrixSdpCanonicalBlockIndex params → MatrixOperator model.space) :
    matrixSdpCanonicalBlockDiagonal params model (fun b => B b + D b) =
      matrixSdpCanonicalBlockDiagonal params model B +
        matrixSdpCanonicalBlockDiagonal params model D := by
  change matrixSdpCanonicalBlockDiagonal params model (B + D) =
    matrixSdpCanonicalBlockDiagonal params model B +
      matrixSdpCanonicalBlockDiagonal params model D
  simpa only [matrixSdpCanonicalBlockDiagonalLinearMap_apply] using
    map_add (matrixSdpCanonicalBlockDiagonalLinearMap params model) B D

/-- Negation of canonical block-diagonal operators is blockwise negation. -/
@[simp] theorem matrixSdpCanonicalBlockDiagonal_neg
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (B : MatrixSdpCanonicalBlockIndex params → MatrixOperator model.space) :
    matrixSdpCanonicalBlockDiagonal params model (fun b => -B b) =
      -matrixSdpCanonicalBlockDiagonal params model B := by
  change matrixSdpCanonicalBlockDiagonal params model (-B) =
    -matrixSdpCanonicalBlockDiagonal params model B
  simpa only [matrixSdpCanonicalBlockDiagonalLinearMap_apply] using
    map_neg (matrixSdpCanonicalBlockDiagonalLinearMap params model) B

/-- Subtraction of canonical block-diagonal operators is blockwise subtraction. -/
@[simp] theorem matrixSdpCanonicalBlockDiagonal_sub
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (B D : MatrixSdpCanonicalBlockIndex params → MatrixOperator model.space) :
    matrixSdpCanonicalBlockDiagonal params model (fun b => B b - D b) =
      matrixSdpCanonicalBlockDiagonal params model B -
        matrixSdpCanonicalBlockDiagonal params model D := by
  change matrixSdpCanonicalBlockDiagonal params model (B - D) =
    matrixSdpCanonicalBlockDiagonal params model B -
      matrixSdpCanonicalBlockDiagonal params model D
  simpa only [matrixSdpCanonicalBlockDiagonalLinearMap_apply] using
    map_sub (matrixSdpCanonicalBlockDiagonalLinearMap params model) B D

/-- Scalar multiplication of canonical block-diagonal operators is blockwise
scalar multiplication. -/
@[simp] theorem matrixSdpCanonicalBlockDiagonal_smul
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (c : ℂ)
    (B : MatrixSdpCanonicalBlockIndex params → MatrixOperator model.space) :
    matrixSdpCanonicalBlockDiagonal params model (fun b => c • B b) =
      c • matrixSdpCanonicalBlockDiagonal params model B := by
  change matrixSdpCanonicalBlockDiagonal params model (c • B) =
    c • matrixSdpCanonicalBlockDiagonal params model B
  simpa only [matrixSdpCanonicalBlockDiagonalLinearMap_apply] using
    map_smul (matrixSdpCanonicalBlockDiagonalLinearMap params model) c B

@[simp] theorem matrixSdpCanonicalDiagonalBlock_blockDiagonal (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (B : MatrixSdpCanonicalBlockIndex params → MatrixOperator model.space)
    (b : MatrixSdpCanonicalBlockIndex params) :
    matrixSdpCanonicalDiagonalBlock params model
        (matrixSdpCanonicalBlockDiagonal params model B) b =
      B b := by
  ext i j
  rw [matrixSdpCanonicalBlockDiagonal_eq_reindex_blockDiagonal]
  simp [matrixSdpCanonicalDiagonalBlock]

/-- The primal slack block `S = I - ∑_g T_g`. -/
noncomputable def matrixSdpCanonicalSlackOperator (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space) :
    MatrixOperator model.space :=
  1 - ∑ g : Polynomial params, T.effect g

/-- The block family associated to the paper primal variable and its slack. -/
noncomputable def matrixSdpCanonicalPrimalBlockFamily (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space) :
    MatrixSdpCanonicalBlockIndex params → MatrixOperator model.space
  | none => matrixSdpCanonicalSlackOperator params model T
  | some g => T.effect g

@[simp] theorem matrixSdpCanonicalPrimalBlockFamily_none (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space) :
    matrixSdpCanonicalPrimalBlockFamily params model T none =
      matrixSdpCanonicalSlackOperator params model T :=
  rfl

@[simp] theorem matrixSdpCanonicalPrimalBlockFamily_some (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (g : Polynomial params) :
    matrixSdpCanonicalPrimalBlockFamily params model T (some g) = T.effect g :=
  rfl

/-- The canonical block matrix associated to the paper primal submeasurement. -/
noncomputable def matrixSdpCanonicalPrimalBlockMatrix (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space) :
    MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model) :=
  matrixSdpCanonicalBlockDiagonal params model
    (matrixSdpCanonicalPrimalBlockFamily params model T)

/-- Feasibility for the canonical primal block SDP: the block variable is
positive semidefinite and satisfies the equality constraint
`X_{none,none} + ∑_g X_{gg} = I`. -/
structure MatrixSdpCanonicalPrimalFeasible (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)) : Prop where
  /-- The canonical primal matrix variable is positive semidefinite. -/
  nonnegative : 0 ≤ X
  /-- The diagonal-block equality constraint holds. -/
  constraintEqOne : matrixSdpCanonicalConstraintOperator params model X = 1

/-- Every diagonal block `X_{bb}` of a positive canonical primal matrix is
positive semidefinite.

This is the formal version of the paper's assertion that, from `X ≥ 0`, each
principal block `X_{ii}` is positive. -/
theorem matrixSdpCanonicalDiagonalBlock_nonneg
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    {X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)}
    (hX : 0 ≤ X)
    (b : MatrixSdpCanonicalBlockIndex params) :
    0 ≤ matrixSdpCanonicalDiagonalBlock params model X b := by
  refine Matrix.nonneg_iff_posSemidef.mpr ?_
  have hpos : Matrix.PosSemidef X := Matrix.nonneg_iff_posSemidef.mp hX
  change Matrix.PosSemidef
    (Matrix.submatrix X
      (fun i : model.space.carrier => (b, i))
      (fun i : model.space.carrier => (b, i)))
  exact hpos.submatrix (fun i : model.space.carrier => (b, i))

/-- The polynomial diagonal blocks of a feasible canonical primal matrix form a
submeasurement total.

The canonical constraint gives `X_{none,none} + ∑_g X_{gg} = I`; since the
slack block `X_{none,none}` is positive, the polynomial blocks satisfy
`∑_g X_{gg} ≤ I`. -/
theorem matrixSdpCanonicalPrimalFeasible_sum_diagonalBlock_some_le_one
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    {X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)}
    (hX : MatrixSdpCanonicalPrimalFeasible params model X) :
    ∑ g : Polynomial params,
        matrixSdpCanonicalDiagonalBlock params model X (some g) ≤
      1 := by
  have hsum :
      matrixSdpCanonicalDiagonalBlock params model X none +
          ∑ g : Polynomial params,
            matrixSdpCanonicalDiagonalBlock params model X (some g) =
        1 := by
    simpa [matrixSdpCanonicalConstraintOperator, Fintype.sum_option] using
      hX.constraintEqOne
  have hslack :
      0 ≤ matrixSdpCanonicalDiagonalBlock params model X none :=
    matrixSdpCanonicalDiagonalBlock_nonneg params model hX.nonnegative none
  calc
    ∑ g : Polynomial params,
        matrixSdpCanonicalDiagonalBlock params model X (some g)
        ≤ matrixSdpCanonicalDiagonalBlock params model X none +
            ∑ g : Polynomial params,
              matrixSdpCanonicalDiagonalBlock params model X (some g) := by
          simpa using add_le_add_right hslack
            (∑ g : Polynomial params,
              matrixSdpCanonicalDiagonalBlock params model X (some g))
    _ = 1 := hsum

/-- The paper primal submeasurement extracted from a feasible canonical primal
matrix by setting `T_g = X_{gg}` on the polynomial blocks. -/
noncomputable def matrixSdpCanonicalExtractedPrimalSubmeasurement
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : MatrixSdpCanonicalPrimalFeasible params model X) :
    MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space where
  effect g := matrixSdpCanonicalDiagonalBlock params model X (some g)
  pos g := matrixSdpCanonicalDiagonalBlock_nonneg params model hX.nonnegative (some g)
  sum_le_one := matrixSdpCanonicalPrimalFeasible_sum_diagonalBlock_some_le_one
    params model hX

@[simp] theorem matrixSdpCanonicalExtractedPrimalSubmeasurement_effect
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : MatrixSdpCanonicalPrimalFeasible params model X)
    (g : Polynomial params) :
    (matrixSdpCanonicalExtractedPrimalSubmeasurement params model X hX).effect g =
      matrixSdpCanonicalDiagonalBlock params model X (some g) :=
  rfl

/-- The slack block of the submeasurement extracted from a feasible canonical
matrix is the original canonical slack diagonal block. -/
theorem matrixSdpCanonicalSlackOperator_extractedPrimalSubmeasurement
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : MatrixSdpCanonicalPrimalFeasible params model X) :
    matrixSdpCanonicalSlackOperator params model
        (matrixSdpCanonicalExtractedPrimalSubmeasurement params model X hX) =
      matrixSdpCanonicalDiagonalBlock params model X none := by
  have hsum :
      matrixSdpCanonicalDiagonalBlock params model X none +
          ∑ g : Polynomial params,
            matrixSdpCanonicalDiagonalBlock params model X (some g) =
        1 := by
    simpa [matrixSdpCanonicalConstraintOperator, Fintype.sum_option] using
      hX.constraintEqOne
  unfold matrixSdpCanonicalSlackOperator
  calc
    1 -
        ∑ g : Polynomial params,
          (matrixSdpCanonicalExtractedPrimalSubmeasurement params model X hX).effect g =
        1 - ∑ g : Polynomial params,
          matrixSdpCanonicalDiagonalBlock params model X (some g) := by
          try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal
    _ = matrixSdpCanonicalDiagonalBlock params model X none := by
          rw [← hsum]
          abel

@[simp] theorem matrixSdpCanonicalDiagonalBlock_primalBlockMatrix_extracted_some
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : MatrixSdpCanonicalPrimalFeasible params model X)
    (g : Polynomial params) :
    matrixSdpCanonicalDiagonalBlock params model
        (matrixSdpCanonicalPrimalBlockMatrix params model
          (matrixSdpCanonicalExtractedPrimalSubmeasurement params model X hX))
        (some g) =
      matrixSdpCanonicalDiagonalBlock params model X (some g) := by
  simp [matrixSdpCanonicalPrimalBlockMatrix]

@[simp] theorem matrixSdpCanonicalDiagonalBlock_primalBlockMatrix_extracted_none
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : MatrixSdpCanonicalPrimalFeasible params model X) :
    matrixSdpCanonicalDiagonalBlock params model
        (matrixSdpCanonicalPrimalBlockMatrix params model
          (matrixSdpCanonicalExtractedPrimalSubmeasurement params model X hX))
        none =
      matrixSdpCanonicalDiagonalBlock params model X none := by
  simpa [matrixSdpCanonicalPrimalBlockMatrix] using
    matrixSdpCanonicalSlackOperator_extractedPrimalSubmeasurement params model X hX

-- vendoring compile fix (Lean v4.33): the previous step may close the goal

end MIPStarRE.LDT.SelfImprovement


