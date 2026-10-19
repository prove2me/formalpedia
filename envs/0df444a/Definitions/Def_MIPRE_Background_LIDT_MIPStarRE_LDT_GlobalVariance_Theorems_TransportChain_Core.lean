-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_TransportChain_Core
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_TransportChain_Core
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T04:04:05.97284+00:00
-- url     : https://prove2.me/theorems/305413a1-f58e-47a8-9bbe-db2b5fdce3f8
-- title:
--   Definitions of Core: Six-step local-variance transport-chain assembly This module assembles the six steps of `lem:local-variance-of-points`…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.GlobalVariance.Theorems.TransportChain.Core` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Six-step local-variance transport-chain assembly. This module assembles the six steps of `lem:local-variance-of-points` (`expansion.tex`, lines 305--311) into a single triangle-inequality bound on the hypercube-edge distribution, producing the main transport estimate `localVarianceTransportChainBound`.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Definitions** (3): `MIPStarRE.LDT.GlobalVariance.TransportQuestion`; `_private.MIPRE.Background.LIDT.MIPStarRE.LDT.GlobalVariance.Theorems.TransportChain.Core.0.MIPStarRE.LDT.GlobalVariance.addCoordLeftEquiv`; `_private.MIPRE.Background.LIDT.MIPStarRE.LDT.GlobalVariance.Theorems.TransportChain.Core.0.MIPStarRE.LDT.GlobalVariance.singletonOpFamily`.
--
--   **Embedded lemmas** (8): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `avgOver_transport_leftPoint`, `avgOver_transport_leftQuestion`, `avgOver_transport_rightPoint`, `avgOver_transport_rightQuestion`, `weightedGeneralizeBRightOperatorAtPolynomial_point_eq`, `localVarianceTransportLinePairBound`, `sddOpRel_singleton_of_bound`, `transportQuestionEquiv_symm_pair`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.GlobalVariance.Theorems.TransportChain.Core` (`MIPRE/Background/LIDT/MIPStarRE/LDT/GlobalVariance/Theorems/TransportChain/Core.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 52 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/GlobalVariance/Theorems/TransportChain/Core.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/GlobalVariance/Theorems/TransportChain/Core.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/GlobalVariance/Theorems/TransportChain/Core.lean (definition bundle: declarations the uploaded statements rest on);
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
import Mathlib.Algebra.BigOperators.Fin
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
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Group.Hom.Defs
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
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
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
import Mathlib.Algebra.Order.Monoid.NatCast
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
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Algebra.Star.StarProjection
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
import Mathlib.Data.FunLike.Embedding
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
import Mathlib.Data.Multiset.Filter
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
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Init
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Operations
import Mathlib.Data.SetLike.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Matrix.CharP
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Reindex
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyRole_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_MeasurementLift
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_ConsistencyBridges
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_CompletionTransfer
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_PolynomialAgreement
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Operators
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Families
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Fourier
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_MatrixRealization_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_MatrixRealization_TraceForms
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Theorems_Foundations
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Theorems_Matrix
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Theorems_Results
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_Averaging
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_Statements
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_AlgebraicIdentity
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_CollisionExpansion
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_SelfConsistencyTransport_PointLine
import Theorems.Thm_MIPStarRE_LDT_GlobalVariance_avgOver_axisParallelLineQuestionDistribution
import Theorems.Thm_MIPStarRE_LDT_GlobalVariance_avgOver_axisParallelLineQuestionDistribution_to_axisParallelTestSample
import Theorems.Thm_MIPStarRE_LDT_GlobalVariance_axisParallelPointLineConsistency_weighted_leftToRightLineQuestion
import Theorems.Thm_MIPStarRE_LDT_GlobalVariance_axisParallelPointLineConsistency_weighted_rightToLeftLineQuestion
import Theorems.Thm_MIPStarRE_LDT_GlobalVariance_ev_adjoint_sub_swap
import Theorems.Thm_MIPStarRE_LDT_GlobalVariance_generalizeBFromSchwartzZippel
import Theorems.Thm_MIPStarRE_LDT_GlobalVariance_generalizeBPointwiseSchwartzZippel
import Theorems.Thm_MIPStarRE_LDT_GlobalVariance_generalizeBReversePointwiseBound
import Theorems.Thm_MIPStarRE_LDT_GlobalVariance_pointConditionedEventSelfConsistency_weighted_point
import Theorems.Thm_MIPStarRE_LDT_Preliminaries_sddOpRel_chain
import Theorems.Thm_MIPStarRE_LDT_avgOver_congr
import Theorems.Thm_MIPStarRE_LDT_avgOver_uniform_fst
import Theorems.Thm_MIPStarRE_LDT_avgOver_uniform_prod

set_option backward.isDefEq.respectTransparency false

namespace MIPStarRE.LDT.GlobalVariance

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
open MIPStarRE.LDT.MakingMeasurementsProjective
open MIPStarRE.LDT.ExpansionHypercubeGraph
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! # Six-step local-variance transport-chain assembly

This module assembles the six steps of `lem:local-variance-of-points`
(`expansion.tex`, lines 305--311) into a single triangle-inequality bound
on the hypercube-edge distribution, producing the main transport estimate
`localVarianceTransportChainBound`.
-/

abbrev TransportQuestion (params : Parameters) [FieldModel params.q] :=
  (AxisParallelLine params × Fq params) × Fq params

noncomputable def singletonOpFamily {Question κ : Type*}
    [Fintype κ] [DecidableEq κ]
    (X : Question → MIPStarRE.Quantum.Op κ) :
    IdxOpFamily Question Unit κ :=
  fun q => { outcome := fun _ => X q, total := X q }

lemma sddOpRel_singleton_of_bound {Question κ : Type*}
    [Fintype κ] [DecidableEq κ]
    (ψ : QuantumState κ) (𝒟 : Distribution Question)
    (X Y : Question → MIPStarRE.Quantum.Op κ) (δ : Error)
    (h :
      avgOver 𝒟 (fun q => ev ψ (((X q - Y q)ᴴ) * (X q - Y q))) ≤ δ) :
    SDDOpRel ψ 𝒟 (singletonOpFamily X) (singletonOpFamily Y) δ := by
  refine ⟨?_⟩
  simpa [sddErrorOp, qSDDOp, qSDDCore, singletonOpFamily] using h

lemma avgOver_transport_leftQuestion
    (params : Parameters) [FieldModel params.q]
    (f : AxisParallelLineQuestion params → Error) :
    avgOver (uniformDistribution (TransportQuestion params))
      (fun q => f (q.1.1, q.1.1.pointAt q.1.2)) =
    avgOver (axisParallelLineQuestionDistribution params) f := by
  calc
    avgOver (uniformDistribution (TransportQuestion params))
        (fun q => f (q.1.1, q.1.1.pointAt q.1.2))
      = avgOver (uniformDistribution (AxisParallelLine params × Fq params))
          (fun ℓt => f (ℓt.1, ℓt.1.pointAt ℓt.2)) := by
          exact avgOver_uniform_fst
            (α := AxisParallelLine params × Fq params) (β := Fq params)
            (fun ℓt => f (ℓt.1, ℓt.1.pointAt ℓt.2))
    _ = avgOver (axisParallelLineQuestionDistribution params) f :=
        (avgOver_axisParallelLineQuestionDistribution params f).symm

lemma avgOver_transport_rightQuestion
    (params : Parameters) [FieldModel params.q]
    (f : AxisParallelLineQuestion params → Error) :
    avgOver (uniformDistribution (TransportQuestion params))
      (fun q => f (q.1.1, q.1.1.pointAt q.2)) =
    avgOver (axisParallelLineQuestionDistribution params) f := by
  calc
    avgOver (uniformDistribution (TransportQuestion params))
        (fun q => f (q.1.1, q.1.1.pointAt q.2))
      = avgOver (uniformDistribution (AxisParallelLine params × Fq params))
          (fun ℓt =>
            avgOver (uniformDistribution (Fq params))
              (fun t => f (ℓt.1, ℓt.1.pointAt t))) := by
          exact avgOver_uniform_prod
            (α := AxisParallelLine params × Fq params) (β := Fq params)
            (f := fun ℓt t => f (ℓt.1, ℓt.1.pointAt t))
    _ = avgOver (uniformDistribution (AxisParallelLine params))
          (fun ℓ =>
            avgOver (uniformDistribution (Fq params))
              (fun t => f (ℓ, ℓ.pointAt t))) := by
          exact avgOver_uniform_fst
            (α := AxisParallelLine params) (β := Fq params)
            (fun ℓ =>
              avgOver (uniformDistribution (Fq params))
                (fun t => f (ℓ, ℓ.pointAt t)))
    _ = avgOver (uniformDistribution (AxisParallelLine params × Fq params))
          (fun ℓt => f (ℓt.1, ℓt.1.pointAt ℓt.2)) := by
          exact (avgOver_uniform_prod
            (α := AxisParallelLine params) (β := Fq params)
            (f := fun ℓ t => f (ℓ, ℓ.pointAt t))).symm
    _ = avgOver (axisParallelLineQuestionDistribution params) f :=
        (avgOver_axisParallelLineQuestionDistribution params f).symm

lemma avgOver_transport_leftPoint
    (params : Parameters) [FieldModel params.q]
    (f : Point params → Error) :
    avgOver (uniformDistribution (TransportQuestion params))
      (fun q => f (q.1.1.pointAt q.1.2)) =
    avgOver (uniformDistribution (Point params)) f := by
  calc
    avgOver (uniformDistribution (TransportQuestion params))
        (fun q => f (q.1.1.pointAt q.1.2))
      = avgOver (axisParallelLineQuestionDistribution params)
          (fun qu => f qu.2) := by
          exact avgOver_transport_leftQuestion params (fun qu => f qu.2)
    _ = avgOver (uniformDistribution (AxisParallelTestSample params))
          (fun s => f s.1) := by
          exact avgOver_axisParallelLineQuestionDistribution_to_axisParallelTestSample
            params (fun s => f s.1)
    _ = avgOver (uniformDistribution (Point params)) f := by
          exact avgOver_uniform_fst (α := Point params) (β := Fin params.m) f

lemma avgOver_transport_rightPoint
    (params : Parameters) [FieldModel params.q]
    (f : Point params → Error) :
    avgOver (uniformDistribution (TransportQuestion params))
      (fun q => f (q.1.1.pointAt q.2)) =
    avgOver (uniformDistribution (Point params)) f := by
  calc
    avgOver (uniformDistribution (TransportQuestion params))
        (fun q => f (q.1.1.pointAt q.2))
      = avgOver (axisParallelLineQuestionDistribution params)
          (fun qu => f qu.2) := by
          exact avgOver_transport_rightQuestion params (fun qu => f qu.2)
    _ = avgOver (uniformDistribution (AxisParallelTestSample params))
          (fun s => f s.1) := by
          exact avgOver_axisParallelLineQuestionDistribution_to_axisParallelTestSample
            params (fun s => f s.1)
    _ = avgOver (uniformDistribution (Point params)) f := by
          exact avgOver_uniform_fst (α := Point params) (β := Fin params.m) f

noncomputable def addCoordLeftEquiv (params : Parameters) [FieldModel params.q]
    (c : Fq params) : Fq params ≃ Fq params where
  toFun := fun x => addCoord c x
  invFun := fun y => subCoord y c
  left_inv := fun x => by
    simp [addCoord, subCoord, decode_encodeScalar]
  right_inv := fun y => addCoord_subCoord_right y c

lemma transportQuestionEquiv_symm_pair
    (params : Parameters) [FieldModel params.q]
    (stx : (AxisParallelTestSample params × Fq params) × Fq params) :
    let e : TransportQuestion params ≃
        (AxisParallelTestSample params × Fq params) × Fq params :=
      Equiv.prodCongr (axisParallelLinePointParamEquiv params) (Equiv.refl (Fq params))
    (((e.symm stx).1.1).pointAt ((e.symm stx).1.2),
        ((e.symm stx).1.1).pointAt (e.symm stx).2) =
      (stx.1.1.1,
        Function.update stx.1.1.1 stx.1.1.2
          (addCoord (subCoord (stx.1.1.1 stx.1.1.2) stx.1.2) stx.2)) := by
  cases stx with
  | mk st x =>
      cases st with
      | mk s t0 =>
          cases s with
          | mk u direction =>
              dsimp [axisParallelLinePointParamEquiv]
              apply Prod.ext
              · ext j
                by_cases hj : j = direction <;>
                  simp [AxisParallelLine.pointAt, hj]
              · ext j
                by_cases hj : j = direction <;>
                  simp [AxisParallelLine.pointAt, Function.update, hj]

-- vendoring compile fix (Lean v4.33): the previous step may close the goal

lemma weightedGeneralizeBRightOperatorAtPolynomial_point_eq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params)
    (ℓ : AxisParallelLine params) (u v : Point params) :
    weightedGeneralizeBRightOperatorAtPolynomial params strategy G g (ℓ, u) =
      weightedGeneralizeBRightOperatorAtPolynomial params strategy G g (ℓ, v) := by
  simp [weightedGeneralizeBRightOperatorAtPolynomial,
    generalizeBRightOperatorAtPolynomial, generalizeBRightEventSubMeasAtPolynomial]

lemma localVarianceTransportLinePairBound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) :
    avgOver (uniformDistribution (TransportQuestion params))
      (fun q =>
        let D := weightedPointConditionedOperatorAtPolynomial params strategy G g
            (q.1.1.pointAt q.1.2) -
          weightedPointConditionedOperatorAtPolynomial params strategy G g
            (q.1.1.pointAt q.2)
        ev strategy.state (Dᴴ * D)) ≤
      localVarianceTransportChainError params eps delta := by
  classical
  let A0 : TransportQuestion params → MIPStarRE.Quantum.Op (ι × ι) := fun q =>
    weightedPointConditionedOperatorAtPolynomial params strategy G g (q.1.1.pointAt q.1.2)
  let A1 : TransportQuestion params → MIPStarRE.Quantum.Op (ι × ι) := fun q =>
    weightedPointConditionedRightOperatorAtPolynomial params strategy G g (q.1.1.pointAt q.1.2)
  let A2 : TransportQuestion params → MIPStarRE.Quantum.Op (ι × ι) := fun q =>
    weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g
      (q.1.1, q.1.1.pointAt q.1.2)
  let A3 : TransportQuestion params → MIPStarRE.Quantum.Op (ι × ι) := fun q =>
    weightedGeneralizeBRightOperatorAtPolynomial params strategy G g
      (q.1.1, q.1.1.pointAt q.1.2)
  let A4 : TransportQuestion params → MIPStarRE.Quantum.Op (ι × ι) := fun q =>
    weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g
      (q.1.1, q.1.1.pointAt q.2)
  let A5 : TransportQuestion params → MIPStarRE.Quantum.Op (ι × ι) := fun q =>
    weightedPointConditionedRightOperatorAtPolynomial params strategy G g (q.1.1.pointAt q.2)
  let A6 : TransportQuestion params → MIPStarRE.Quantum.Op (ι × ι) := fun q =>
    weightedPointConditionedOperatorAtPolynomial params strategy G g (q.1.1.pointAt q.2)
  let 𝒟 := uniformDistribution (TransportQuestion params)
  have h01 : SDDOpRel strategy.state 𝒟
      (singletonOpFamily A0) (singletonOpFamily A1) (2 * delta) := by
    refine sddOpRel_singleton_of_bound strategy.state 𝒟 A0 A1 (2 * delta) ?_
    calc
      avgOver 𝒟 (fun q => ev strategy.state (((A0 q - A1 q)ᴴ) * (A0 q - A1 q)))
        = avgOver (uniformDistribution (Point params))
            (fun u =>
              let D := weightedPointConditionedOperatorAtPolynomial params strategy G g u -
                weightedPointConditionedRightOperatorAtPolynomial params strategy G g u
              ev strategy.state (Dᴴ * D)) := by
            exact avgOver_transport_leftPoint params (fun u =>
              let D := weightedPointConditionedOperatorAtPolynomial params strategy G g u -
                weightedPointConditionedRightOperatorAtPolynomial params strategy G g u
              ev strategy.state (Dᴴ * D))
      _ ≤ 2 * delta := pointConditionedEventSelfConsistency_weighted_point
        params strategy eps delta gamma hgood G g
  have h12 : SDDOpRel strategy.state 𝒟
      (singletonOpFamily A1) (singletonOpFamily A2) (2 * eps) := by
    refine sddOpRel_singleton_of_bound strategy.state 𝒟 A1 A2 (2 * eps) ?_
    calc
      avgOver 𝒟 (fun q => ev strategy.state (((A1 q - A2 q)ᴴ) * (A1 q - A2 q)))
        = avgOver (axisParallelLineQuestionDistribution params)
            (fun qu =>
              let D := weightedPointConditionedRightOperatorAtPolynomial
                  params strategy G g qu.2 -
                weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu
              ev strategy.state (Dᴴ * D)) := by
            exact avgOver_transport_leftQuestion params (fun qu =>
              let D := weightedPointConditionedRightOperatorAtPolynomial
                  params strategy G g qu.2 -
                weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu
              ev strategy.state (Dᴴ * D))
      _ ≤ 2 * eps := axisParallelPointLineConsistency_weighted_rightToLeftLineQuestion
        params strategy eps delta gamma hgood G g
  have h23 : SDDOpRel strategy.state 𝒟
      (singletonOpFamily A2) (singletonOpFamily A3) (generalizeBError params) := by
    refine sddOpRel_singleton_of_bound strategy.state 𝒟 A2 A3 (generalizeBError params) ?_
    calc
      avgOver 𝒟 (fun q => ev strategy.state (((A2 q - A3 q)ᴴ) * (A2 q - A3 q)))
        = avgOver (axisParallelLineQuestionDistribution params)
            (fun qu =>
              let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
                weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu
              ev strategy.state (Dᴴ * D)) := by
            exact avgOver_transport_leftQuestion params (fun qu =>
              let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
                weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu
              ev strategy.state (Dᴴ * D))
      _ ≤ generalizeBError params := by
            simpa [generalizeBDeviationAtPolynomial] using
              generalizeBPointwiseSchwartzZippel params strategy G g
  have h34 : SDDOpRel strategy.state 𝒟
      (singletonOpFamily A3) (singletonOpFamily A4) (generalizeBError params) := by
    refine sddOpRel_singleton_of_bound strategy.state 𝒟 A3 A4 (generalizeBError params) ?_
    calc
      avgOver 𝒟 (fun q => ev strategy.state (((A3 q - A4 q)ᴴ) * (A3 q - A4 q)))
        = avgOver 𝒟
            (fun q =>
              let D := weightedGeneralizeBRightOperatorAtPolynomial params strategy G g
                  (q.1.1, q.1.1.pointAt q.2) -
                weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g
                  (q.1.1, q.1.1.pointAt q.2)
              ev strategy.state (Dᴴ * D)) := by
            apply avgOver_congr
            intro q
            dsimp [A3, A4]
            rw [weightedGeneralizeBRightOperatorAtPolynomial_point_eq
              params strategy G g q.1.1 (q.1.1.pointAt q.1.2) (q.1.1.pointAt q.2)]
      _ = avgOver (axisParallelLineQuestionDistribution params)
            (fun qu =>
              let D := weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu -
                weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu
              ev strategy.state (Dᴴ * D)) := by
            exact avgOver_transport_rightQuestion params (fun qu =>
              let D := weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu -
                weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu
              ev strategy.state (Dᴴ * D))
      _ ≤ generalizeBError params := by
            exact generalizeBReversePointwiseBound params strategy strategy.state G
              (generalizeBFromSchwartzZippel params strategy eps delta gamma hgood G) g
  have h45 : SDDOpRel strategy.state 𝒟
      (singletonOpFamily A4) (singletonOpFamily A5) (2 * eps) := by
    refine sddOpRel_singleton_of_bound strategy.state 𝒟 A4 A5 (2 * eps) ?_
    calc
      avgOver 𝒟 (fun q => ev strategy.state (((A4 q - A5 q)ᴴ) * (A4 q - A5 q)))
        = avgOver (axisParallelLineQuestionDistribution params)
            (fun qu =>
              let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
                weightedPointConditionedRightOperatorAtPolynomial params strategy G g qu.2
              ev strategy.state (Dᴴ * D)) := by
            exact avgOver_transport_rightQuestion params (fun qu =>
              let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
                weightedPointConditionedRightOperatorAtPolynomial params strategy G g qu.2
              ev strategy.state (Dᴴ * D))
      _ ≤ 2 * eps := axisParallelPointLineConsistency_weighted_leftToRightLineQuestion
        params strategy eps delta gamma hgood G g
  have h56 : SDDOpRel strategy.state 𝒟
      (singletonOpFamily A5) (singletonOpFamily A6) (2 * delta) := by
    refine sddOpRel_singleton_of_bound strategy.state 𝒟 A5 A6 (2 * delta) ?_
    calc
      avgOver 𝒟 (fun q => ev strategy.state (((A5 q - A6 q)ᴴ) * (A5 q - A6 q)))
        = avgOver 𝒟 (fun q => ev strategy.state (((A6 q - A5 q)ᴴ) * (A6 q - A5 q))) := by
            apply avgOver_congr
            intro q
            exact ev_adjoint_sub_swap strategy.state (A6 q) (A5 q)
      _ = avgOver (uniformDistribution (Point params))
            (fun u =>
              let D := weightedPointConditionedOperatorAtPolynomial params strategy G g u -
                weightedPointConditionedRightOperatorAtPolynomial params strategy G g u
              ev strategy.state (Dᴴ * D)) := by
            exact avgOver_transport_rightPoint params (fun u =>
              let D := weightedPointConditionedOperatorAtPolynomial params strategy G g u -
                weightedPointConditionedRightOperatorAtPolynomial params strategy G g u
              ev strategy.state (Dᴴ * D))
      _ ≤ 2 * delta := pointConditionedEventSelfConsistency_weighted_point
        params strategy eps delta gamma hgood G g
  let families : Fin 7 → IdxOpFamily (TransportQuestion params) Unit (ι × ι) := fun i =>
    if i = 0 then singletonOpFamily A0
    else if i = 1 then singletonOpFamily A1
    else if i = 2 then singletonOpFamily A2
    else if i = 3 then singletonOpFamily A3
    else if i = 4 then singletonOpFamily A4
    else if i = 5 then singletonOpFamily A5
    else singletonOpFamily A6
  let errors : Fin 6 → Error := fun i =>
    if i = 0 then 2 * delta
    else if i = 1 then 2 * eps
    else if i = 2 then generalizeBError params
    else if i = 3 then generalizeBError params
    else if i = 4 then 2 * eps
    else 2 * delta
  have hsteps : ∀ i : Fin 6,
      SDDOpRel strategy.state 𝒟 (families i.castSucc) (families i.succ)
        (errors i) := by
    intro i
    fin_cases i <;> simp [families, errors, h01, h12, h23, h34, h45, h56]
  have hchain := sddOpRel_chain strategy.state 𝒟 6 families errors hsteps
  have hsum :
      (∑ i : Fin 6, errors i) =
        4 * eps + 4 * delta + 2 * generalizeBError params := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
      Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_one]
    simp [errors]
    ring
  have hbound :
      sddErrorOp strategy.state 𝒟 (singletonOpFamily A0) (singletonOpFamily A6) ≤
        localVarianceTransportChainError params eps delta := by
    calc
      sddErrorOp strategy.state 𝒟 (singletonOpFamily A0) (singletonOpFamily A6)
        = sddErrorOp strategy.state 𝒟 (families 0) (families (Fin.last 6)) := by
            simp [families]
      _ ≤ (6 : Error) * ∑ i : Fin 6, errors i := hchain.squaredDistanceBound
      _ = localVarianceTransportChainError params eps delta := by
            rw [hsum]
            simp [localVarianceTransportChainError]
  simpa [sddErrorOp, qSDDOp, qSDDCore, singletonOpFamily, A0, A6, 𝒟] using hbound

end MIPStarRE.LDT.GlobalVariance


