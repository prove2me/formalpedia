-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_LocalityPreservingRepair
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_LocalityPreservingRepair
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T04:39:37.223978+00:00
-- url     : https://prove2.me/theorems/a012fe60-f35d-4f6e-855c-7a23954eef20
-- title:
--   Definitions of LocalityPreservingRepair: Section 5 — Locality-preserving projectivization repair This file proves the locality-preserving repair route for the…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.LocalityPreservingRepair` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Section 5 — Locality-preserving projectivization repair. This file proves the locality-preserving repair route for the late Section 5 `Q/X/XHat/P` argument.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Definitions** (6): `_private.MIPRE.Background.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.LocalityPreservingRepair.0.MIPStarRE.LDT.MakingMeasurementsProjective.diagBlock`; `_private.MIPRE.Background.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.LocalityPreservingRepair.0.MIPStarRE.LDT.MakingMeasurementsProjective.leftMarginalDensity`; `_private.MIPRE.Background.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.LocalityPreservingRepair.0.MIPStarRE.LDT.MakingMeasurementsProjective.leftMarginalState`; `_private.MIPRE.Background.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.LocalityPreservingRepair.0.MIPStarRE.LDT.MakingMeasurementsProjective.rightDiagBlock`; `_private.MIPRE.Background.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.LocalityPreservingRepair.0.MIPStarRE.LDT.MakingMeasurementsProjective.rightMarginalDensity`; `_private.MIPRE.Background.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.LocalityPreservingRepair.0.MIPStarRE.LDT.MakingMeasurementsProjective.rightMarginalState`.
--
--   **Embedded lemmas** (18): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `leftMarginalDensity_nonneg`, `leftMarginalState_isNormalized`, `leftMarginal_ev_eq`, `leftTensor_eq_blockDiagonal_const`, `matrix_eq_zero_of_rank_eq_zero`, `normalizedTrace_leftMarginalDensity_mul_eq`, `normalizedTrace_rightMarginalDensity_mul_eq`, `one_le_orthonormalizationMainLemmaError_of_quarter_lt`, `projectivizationRepair_small_error_bound`, `rightMarginalDensity_nonneg`, ….
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.LocalityPreservingRepair` (`MIPRE/Background/LIDT/MIPStarRE/LDT/MakingMeasurementsProjective/LocalityPreservingRepair.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 45 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/MakingMeasurementsProjective/LocalityPreservingRepair.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/MakingMeasurementsProjective/LocalityPreservingRepair.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/MakingMeasurementsProjective/LocalityPreservingRepair.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.NonUnitalHom
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharP.Invertible
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.IsField
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Action.Opposite
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.Group.Invertible.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Opposite
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.Group.Subsemigroup.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.Algebra.GroupWithZero.Invertible
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.Algebra.Module.Torsion.Pi
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
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Ring.CompTypeclasses
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Unitary
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.CStarAlgebra.Module.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Real.Spectrum
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Countable.Defs
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finset.Attach
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Embedding
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.List.Nodup
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Multiset.Bind
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Multiset.Defs
import Mathlib.Data.Multiset.MapFold
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
import Mathlib.Data.Quot
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
import Mathlib.Data.Set.CoeSort
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Set.Operations
import Mathlib.Data.Set.Restrict
import Mathlib.Data.SetLike.Basic
import Mathlib.Data.Sigma.Basic
import Mathlib.Data.ULift
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Basic
import Mathlib.Logic.Embedding.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set
import Mathlib.Logic.Function.Defs
import Mathlib.Logic.IsEmpty.Basic
import Mathlib.Logic.IsEmpty.Defs
import Mathlib.Logic.Nonempty
import Mathlib.Logic.Nontrivial.Defs
import Mathlib.Logic.Unique
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Order.Basic
import Mathlib.Order.BooleanAlgebra.Defs
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Hom.Basic
import Mathlib.Order.Lattice
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.MinMax
import Mathlib.Order.Nat
import Mathlib.Order.Notation
import Mathlib.Order.RelClasses
import Mathlib.Order.SetNotation
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.RingTheory.Bialgebra.Basic
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.RealSqrt
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
import Mathlib.Topology.ContinuousMap.ContinuousSqrt
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.EMetricSpace.Defs
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.Real
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.GDelta
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Separation.Regular
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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_CompletionTransfer
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_ProjectorONB
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_RankReduction_Sigma
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_RankReduction_LowRank
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_QCompleteness
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_PositiveGram_Rows
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_PositiveGram_Completion
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_LayerAlgebra
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_ProjectorApprox
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_SpectralTruncation_ProjectiveNonMeasurement
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_SpectralTruncation_Conversion
import Theorems.Thm_MIPStarRE_LDT_MakingMeasurementsProjective_spectralTruncationError_le_zetaQuarterRoot
import Theorems.Thm_MIPStarRE_LDT_MakingMeasurementsProjective_zetaQuarterRoot_nonneg
import Theorems.Thm_MIPStarRE_LDT_avgOver_congr
import Theorems.Thm_MIPStarRE_LDT_leftTensor_one
import Theorems.Thm_MIPStarRE_LDT_rightTensor_mul_rightTensor
import Theorems.Thm_MIPStarRE_LDT_rightTensor_one
import Theorems.Thm_MIPStarRE_LDT_rightTensor_sub

set_option backward.isDefEq.respectTransparency false

/-!
# Section 5 — Locality-preserving projectivization repair

This file proves the locality-preserving repair route for the late Section 5
`Q/X/XHat/P` argument.

## Scope

The **spectral-truncation stage** (the first part of the proof of rounding
to projectors) is already proved by
`spectralTruncationStatement_of_sourceAlmostProjective` in
`MakingMeasurementsProjective/SpectralTruncation/ProjectiveNonMeasurement.lean`,
which is fully proved via
`projectiveNonMeasurement_of_sourceAlmostProjective_full`. Proofs that
require the spectral truncation statement should call that declaration directly.

The main result recorded here:

- **`leftLiftedProjectivizationRepair`** — paper origin
  `references/ldt-paper/orthonormalization.tex` lines 534–860 (rank
  reduction and the `Q`/`√Q` completeness setup) and 862–1194 (the
  `X`/`X̂`/`P` algebra producing the lifted projective sub-measurement,
  including the final triangle-inequality assembly).  The formal proof below
  follows that local `Q/X/XHat/P` route by passing to the left marginal state,
  constructing the local projective family there, and transporting the final
  estimate back to left lifts.

The theorem proved here is the direct output of that route under a normalized
bipartite state and the source almost-projective estimate for the left-lifted
measurement. It is stated directly in terms of this estimate, rather than in
terms of a separate repair-input assumption, and provides the unconditional
repair step used by the orthonormalization theorem.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

noncomputable section

def diagBlock {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (M : MIPStarRE.Quantum.Op (ιA × ιB)) (b : ιB) :
    MIPStarRE.Quantum.Op ιA :=
  M.submatrix (fun i => (i, b)) (fun j => (j, b))

def leftMarginalDensity {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ρ : MIPStarRE.Quantum.Op (ιA × ιB)) : MIPStarRE.Quantum.Op ιA :=
  ((((Fintype.card ιB : Error) : Error)⁻¹ : Error) : ℂ) •
    ∑ b : ιB, diagBlock ρ b

lemma leftMarginalDensity_nonneg {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    {ρ : MIPStarRE.Quantum.Op (ιA × ιB)} (hρ : 0 ≤ ρ) :
    0 ≤ leftMarginalDensity ρ := by
  have hρpsd : ρ.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hρ
  have hsum : 0 ≤ ∑ b : ιB, diagBlock ρ b := by
    refine Finset.sum_nonneg fun b _ => ?_
    refine Matrix.nonneg_iff_posSemidef.mpr ?_
    simpa [diagBlock] using hρpsd.submatrix (fun i => (i, b))
  have hcoeff : 0 ≤ ((((Fintype.card ιB : Error) : Error)⁻¹ : Error) : ℂ) := by
    positivity
  simpa [leftMarginalDensity] using smul_nonneg hcoeff hsum

def leftMarginalState {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB)) : QuantumState ιA where
  density := leftMarginalDensity ψ.density
  density_psd := leftMarginalDensity_nonneg ψ.density_psd

lemma leftTensor_eq_blockDiagonal_const {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (X : MIPStarRE.Quantum.Op ιA) :
    leftTensor (ι₂ := ιB) X = Matrix.blockDiagonal (fun _ : ιB => X) := by
  ext x y
  rcases x with ⟨i, b⟩
  rcases y with ⟨j, c⟩
  by_cases h : b = c
  · subst c
    simp [leftTensor, Matrix.blockDiagonal_apply]
  · simp [leftTensor, Matrix.blockDiagonal_apply, h]

lemma trace_blockDiagonal_const_mul_eq_sum_trace_diagBlock
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (X : MIPStarRE.Quantum.Op ιA)
    (M : MIPStarRE.Quantum.Op (ιA × ιB)) :
    Matrix.trace (Matrix.blockDiagonal (fun _ : ιB => X) * M) =
      ∑ b : ιB, Matrix.trace (X * diagBlock M b) := by
  classical
  let e : ((ιA × ιB) × ιA) ≃ (ιB × (ιA × ιA)) :=
    { toFun := fun x => (x.1.2, (x.1.1, x.2))
      invFun := fun x => ((x.2.1, x.1), x.2.2)
      left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
      right_inv := fun ⟨_, ⟨_, _⟩⟩ => rfl }
  simpa [diagBlock, Matrix.trace, Matrix.mul_apply, Matrix.blockDiagonal_apply,
    Fintype.sum_prod_type, Finset.sum_sigma', e] using
    (e.sum_comp (fun y : ιB × (ιA × ιA) =>
      X y.2.1 y.2.2 * M (y.2.2, y.1) (y.2.1, y.1)))

lemma normalizedTrace_leftMarginalDensity_mul_eq
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ρ : MIPStarRE.Quantum.Op (ιA × ιB)) (X : MIPStarRE.Quantum.Op ιA) :
    MIPStarRE.Quantum.normalizedTrace (leftMarginalDensity ρ * X) =
      MIPStarRE.Quantum.normalizedTrace (ρ * leftTensor (ι₂ := ιB) X) := by
  have hcard : ((Fintype.card ιB : Error) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold MIPStarRE.Quantum.normalizedTrace leftMarginalDensity
  rw [smul_mul_assoc, Matrix.trace_smul, Matrix.sum_mul, Matrix.trace_sum]
  have hswap :
      ∑ b : ιB, Matrix.trace (diagBlock ρ b * X) =
        ∑ b : ιB, Matrix.trace (X * diagBlock ρ b) := by
    refine Finset.sum_congr rfl ?_
    intro b _
    exact Matrix.trace_mul_comm _ _
  rw [hswap]
  rw [Matrix.trace_mul_comm]
  rw [leftTensor_eq_blockDiagonal_const]
  rw [trace_blockDiagonal_const_mul_eq_sum_trace_diagBlock]
  simp [Fintype.card_prod]
  ring

lemma leftMarginalState_isNormalized {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    {ψ : QuantumState (ιA × ιB)} (hψ : ψ.IsNormalized) :
    (leftMarginalState ψ).IsNormalized := by
  unfold QuantumState.IsNormalized
  have hnorm :
      MIPStarRE.Quantum.normalizedTrace (leftMarginalDensity ψ.density) =
        MIPStarRE.Quantum.normalizedTrace ψ.density := by
    simpa [leftTensor_one] using
      normalizedTrace_leftMarginalDensity_mul_eq (ρ := ψ.density)
        (X := (1 : MIPStarRE.Quantum.Op ιA))
  simpa [leftMarginalState] using hnorm.trans hψ

lemma leftMarginal_ev_eq {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB)) (X : MIPStarRE.Quantum.Op ιA) :
    ev ψ (leftTensor (ι₂ := ιB) X) = ev (leftMarginalState ψ) X := by
  unfold ev
  rw [← Complex.ofReal_inj]
  simp [normalizedTrace_leftMarginalDensity_mul_eq (ρ := ψ.density) (X := X),
    leftMarginalState]

def rightDiagBlock {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (M : MIPStarRE.Quantum.Op (ιA × ιB)) (a : ιA) :
    MIPStarRE.Quantum.Op ιB :=
  M.submatrix (fun i => (a, i)) (fun j => (a, j))

def rightMarginalDensity {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Nonempty ιA]
    (ρ : MIPStarRE.Quantum.Op (ιA × ιB)) : MIPStarRE.Quantum.Op ιB :=
  ((((Fintype.card ιA : Error) : Error)⁻¹ : Error) : ℂ) •
    ∑ a : ιA, rightDiagBlock ρ a

lemma rightMarginalDensity_nonneg {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Nonempty ιA]
    {ρ : MIPStarRE.Quantum.Op (ιA × ιB)} (hρ : 0 ≤ ρ) :
    0 ≤ rightMarginalDensity ρ := by
  have hρpsd : ρ.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hρ
  have hsum : 0 ≤ ∑ a : ιA, rightDiagBlock ρ a := by
    refine Finset.sum_nonneg fun a _ => ?_
    refine Matrix.nonneg_iff_posSemidef.mpr ?_
    simpa [rightDiagBlock] using hρpsd.submatrix (fun i => (a, i))
  have hcoeff : 0 ≤ ((((Fintype.card ιA : Error) : Error)⁻¹ : Error) : ℂ) := by
    positivity
  simpa [rightMarginalDensity] using smul_nonneg hcoeff hsum

def rightMarginalState {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Nonempty ιA]
    (ψ : QuantumState (ιA × ιB)) : QuantumState ιB where
  density := rightMarginalDensity ψ.density
  density_psd := rightMarginalDensity_nonneg ψ.density_psd

lemma trace_mul_rightTensor_eq_sum_trace_rightDiagBlock
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (M : MIPStarRE.Quantum.Op (ιA × ιB)) (X : MIPStarRE.Quantum.Op ιB) :
    Matrix.trace (M * rightTensor (ι₁ := ιA) X) =
      ∑ a : ιA, Matrix.trace (rightDiagBlock M a * X) := by
  classical
  let e : ((ιA × ιB) × ιB) ≃ (ιA × (ιB × ιB)) :=
    { toFun := fun x => (x.1.1, (x.1.2, x.2))
      invFun := fun x => ((x.1, x.2.1), x.2.2)
      left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
      right_inv := fun ⟨_, ⟨_, _⟩⟩ => rfl }
  simpa [rightDiagBlock, Matrix.trace, Matrix.mul_apply, rightTensor, Matrix.one_apply,
    Fintype.sum_prod_type, Finset.sum_sigma', e] using
    (e.sum_comp (fun y : ιA × (ιB × ιB) =>
      M (y.1, y.2.1) (y.1, y.2.2) * X y.2.2 y.2.1))

lemma normalizedTrace_rightMarginalDensity_mul_eq
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Nonempty ιA]
    (ρ : MIPStarRE.Quantum.Op (ιA × ιB)) (X : MIPStarRE.Quantum.Op ιB) :
    MIPStarRE.Quantum.normalizedTrace (rightMarginalDensity ρ * X) =
      MIPStarRE.Quantum.normalizedTrace (ρ * rightTensor (ι₁ := ιA) X) := by
  have hcard : ((Fintype.card ιA : Error) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold MIPStarRE.Quantum.normalizedTrace rightMarginalDensity
  rw [smul_mul_assoc, Matrix.trace_smul, Matrix.sum_mul, Matrix.trace_sum]
  rw [trace_mul_rightTensor_eq_sum_trace_rightDiagBlock]
  simp [Fintype.card_prod]
  ring

lemma rightMarginalState_isNormalized {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Nonempty ιA]
    {ψ : QuantumState (ιA × ιB)} (hψ : ψ.IsNormalized) :
    (rightMarginalState ψ).IsNormalized := by
  unfold QuantumState.IsNormalized
  have hnorm :
      MIPStarRE.Quantum.normalizedTrace (rightMarginalDensity ψ.density) =
        MIPStarRE.Quantum.normalizedTrace ψ.density := by
    simpa [rightTensor_one] using
      normalizedTrace_rightMarginalDensity_mul_eq (ρ := ψ.density)
        (X := (1 : MIPStarRE.Quantum.Op ιB))
  simpa [rightMarginalState] using hnorm.trans hψ

lemma rightMarginal_ev_eq {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Nonempty ιA]
    (ψ : QuantumState (ιA × ιB)) (X : MIPStarRE.Quantum.Op ιB) :
    ev ψ (rightTensor (ι₁ := ιA) X) = ev (rightMarginalState ψ) X := by
  unfold ev
  rw [← Complex.ofReal_inj]
  simp [normalizedTrace_rightMarginalDensity_mul_eq (ρ := ψ.density) (X := X),
    rightMarginalState]

/-- Scalar absorption used inside the locality-preserving projectivization repair.

Paper origin: `references/ldt-paper/orthonormalization.tex:862-1194`, where the
local \(Q/X/\widehat X/P\) construction is combined by the triangle inequality
and then absorbed into the displayed \(84\zeta^{1/4}\) envelope.

**Faithful encoding:** This is an internal scalar estimate for the proved
locality-preserving construction, not an additional hypothesis of the source
orthonormalization theorem. -/
lemma projectivizationRepair_small_error_bound {ζ : Error}
    (hζ : 0 ≤ ζ) (hζ_small : ζ ≤ 1 / (4 : Error)) :
    2 * (roundingToProjectiveError ζ + 30 * zetaQuarterRoot ζ) ≤
      orthonormalizationMainLemmaError ζ := by
  have htrunc : spectralTruncationError ζ ≤ zetaQuarterRoot ζ :=
    spectralTruncationError_le_zetaQuarterRoot ζ hζ hζ_small
  have hround : roundingToProjectiveError ζ ≤ 12 * zetaQuarterRoot ζ := by
    dsimp [roundingToProjectiveError]
    gcongr
    simpa [spectralTruncationError, zetaQuarterRoot] using htrunc
  calc
    2 * (roundingToProjectiveError ζ + 30 * zetaQuarterRoot ζ)
        ≤ 2 * (12 * zetaQuarterRoot ζ + 30 * zetaQuarterRoot ζ) := by
            gcongr
    _ = orthonormalizationMainLemmaError ζ := by
          dsimp [orthonormalizationMainLemmaError, zetaQuarterRoot]
          ring

lemma roundingToProjectiveError_le_orthonormalizationMainLemmaError {ζ : Error}
    (hζ : 0 ≤ ζ) (hζ_small : ζ ≤ 1 / (4 : Error)) :
    roundingToProjectiveError ζ ≤ orthonormalizationMainLemmaError ζ := by
  have htrunc : spectralTruncationError ζ ≤ zetaQuarterRoot ζ :=
    spectralTruncationError_le_zetaQuarterRoot ζ hζ hζ_small
  calc
    roundingToProjectiveError ζ ≤ 12 * zetaQuarterRoot ζ := by
      dsimp [roundingToProjectiveError]
      gcongr
      simpa [spectralTruncationError, zetaQuarterRoot] using htrunc
    _ ≤ orthonormalizationMainLemmaError ζ := by
      dsimp [orthonormalizationMainLemmaError, zetaQuarterRoot]
      exact mul_le_mul_of_nonneg_right (by norm_num : (12 : Error) ≤ 84)
        (zetaQuarterRoot_nonneg hζ)

lemma one_le_orthonormalizationMainLemmaError_of_quarter_lt {ζ : Error}
    (hquarter_lt : (1 / (4 : Error)) < ζ) :
    1 ≤ orthonormalizationMainLemmaError ζ := by
  have hq_rpow_le :
      Real.rpow (1 / (4 : Error)) (1 / (4 : Error)) ≤
        Real.rpow ζ (1 / (4 : Error)) := by
    exact Real.rpow_le_rpow (by positivity) (le_of_lt hquarter_lt) (by positivity)
  have hquarter_le_rpow :
      (1 / (4 : Error)) ≤ Real.rpow (1 / (4 : Error)) (1 / (4 : Error)) := by
    simpa [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_ge'
        (show 0 ≤ (1 / (4 : Error)) by positivity)
        (show (1 / (4 : Error)) ≤ 1 by norm_num)
        (show 0 ≤ (1 / (4 : Error)) by positivity)
        (by norm_num : (1 / (4 : Error)) ≤ 1))
  have hquarter_le : (1 / (4 : Error)) ≤ Real.rpow ζ (1 / (4 : Error)) :=
    le_trans hquarter_le_rpow hq_rpow_le
  have hscaled : (84 : Error) * (1 / (4 : Error)) ≤ orthonormalizationMainLemmaError ζ := by
    dsimp [orthonormalizationMainLemmaError]
    exact mul_le_mul_of_nonneg_left hquarter_le (by norm_num)
  have hone : (1 : Error) ≤ (84 : Error) * (1 / (4 : Error)) := by norm_num
  exact hone.trans hscaled

lemma matrix_eq_zero_of_rank_eq_zero {m n : Type*}
    [Finite m] [Fintype n] (A : Matrix m n ℂ) (hA : A.rank = 0) :
    A = 0 := by
  let _ : Fintype m := Fintype.ofFinite m
  classical
  have hrange : A.mulVecLin.range = ⊥ := by
    rw [Matrix.rank] at hA
    exact Submodule.finrank_eq_zero.mp hA
  ext i j
  have hv : A.mulVecLin (Pi.single j 1) ∈ A.mulVecLin.range := ⟨Pi.single j 1, rfl⟩
  have hv0 : A.mulVecLin (Pi.single j 1) = 0 := by
    simpa [hrange] using hv
  have hentry := congrArg (fun w => w i) hv0
  simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Finset.sum_ite_eq,
    Pi.single_apply] using hentry

lemma sddRel_of_leftPlaced_sddOpRel {Outcome : Type*}
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    {ψ : QuantumState (ιA × ιB)} {A : Measurement Outcome ιA}
    {R : OpFamily Outcome ιA}
    {P : ProjSubMeas Outcome ιA}
    {δ : Error}
    (hR : ∀ a : Outcome, R.outcome a = P.outcome a)
    (hclose :
      SDDOpRel ψ (uniformDistribution Unit)
        (fun _ => OpFamily.leftPlacedOpFamily (ιB := ιB) (A.toSubMeas : OpFamily Outcome ιA))
        (fun _ => OpFamily.leftPlacedOpFamily (ιB := ιB) R)
        δ) :
    SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) A.toSubMeas))
      (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) P.toSubMeas))
      δ := by
  refine ⟨?_⟩
  have herror :
      sddError ψ (uniformDistribution Unit)
          (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) A.toSubMeas))
          (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) P.toSubMeas)) =
        sddErrorOp ψ (uniformDistribution Unit)
          (fun _ => OpFamily.leftPlacedOpFamily (ιB := ιB) (A.toSubMeas : OpFamily Outcome ιA))
          (fun _ => OpFamily.leftPlacedOpFamily (ιB := ιB) R) := by
    unfold sddError sddErrorOp
    refine avgOver_congr (uniformDistribution Unit) _ _ ?_
    intro u
    unfold qSDD qSDDOp qSDDCore
    refine Finset.sum_congr rfl ?_
    intro a _
    simp [constSubMeasFamily, leftPlacedSubMeas, SubMeas.toOpFamily,
      OpFamily.leftPlacedOpFamily, hR a]
  rw [herror]
  exact hclose.squaredDistanceBound

lemma sddOpRel_rightPlaced_of_ev_eq
    {Question Outcome : Type*} {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB)) (φ : QuantumState ιB)
    (𝒟 : Distribution Question)
    (A B : IdxOpFamily Question Outcome ιB) (δ : Error)
    (hev : ∀ X : MIPStarRE.Quantum.Op ιB,
      ev ψ (rightTensor (ι₁ := ιA) X) = ev φ X) :
    SDDOpRel φ 𝒟 A B δ →
    SDDOpRel ψ 𝒟
      (fun q => OpFamily.rightPlacedOpFamily (ιA := ιA) (A q))
      (fun q => OpFamily.rightPlacedOpFamily (ιA := ιA) (B q)) δ := by
  intro ⟨hAB⟩
  constructor
  unfold sddErrorOp at *
  calc
    avgOver 𝒟
        (fun q =>
          qSDDOp ψ
            (OpFamily.rightPlacedOpFamily (ιA := ιA) (A q))
            (OpFamily.rightPlacedOpFamily (ιA := ιA) (B q)))
      = avgOver 𝒟 (fun q => qSDDOp φ (A q) (B q)) := by
          refine avgOver_congr 𝒟 _ _ ?_
          intro q
          unfold qSDDOp qSDDCore
          refine Finset.sum_congr rfl ?_
          intro a _
          simp [OpFamily.rightPlacedOpFamily, rightTensor_sub,
            rightTensor_mul_rightTensor, hev]
    _ ≤ δ := hAB

lemma sddRel_of_rightPlaced_sddOpRel {Outcome : Type*}
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    {ψ : QuantumState (ιA × ιB)} {B : Measurement Outcome ιB}
    {R : OpFamily Outcome ιB}
    {P : ProjSubMeas Outcome ιB}
    {δ : Error}
    (hR : ∀ a : Outcome, R.outcome a = P.outcome a)
    (hclose :
      SDDOpRel ψ (uniformDistribution Unit)
        (fun _ => OpFamily.rightPlacedOpFamily (ιA := ιA) (B.toSubMeas : OpFamily Outcome ιB))
        (fun _ => OpFamily.rightPlacedOpFamily (ιA := ιA) R)
        δ) :
    SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) B.toSubMeas))
      (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) P.toSubMeas))
      δ := by
  refine ⟨?_⟩
  have herror :
      sddError ψ (uniformDistribution Unit)
          (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) B.toSubMeas))
          (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) P.toSubMeas)) =
        sddErrorOp ψ (uniformDistribution Unit)
          (fun _ => OpFamily.rightPlacedOpFamily (ιA := ιA) (B.toSubMeas : OpFamily Outcome ιB))
          (fun _ => OpFamily.rightPlacedOpFamily (ιA := ιA) R) := by
    unfold sddError sddErrorOp
    refine avgOver_congr (uniformDistribution Unit) _ _ ?_
    intro u
    unfold qSDD qSDDOp qSDDCore
    refine Finset.sum_congr rfl ?_
    intro a _
    simp [constSubMeasFamily, rightPlacedSubMeas, SubMeas.toOpFamily,
      OpFamily.rightPlacedOpFamily, hR a]
  rw [herror]
  exact hclose.squaredDistanceBound

end

end MIPStarRE.LDT.MakingMeasurementsProjective


