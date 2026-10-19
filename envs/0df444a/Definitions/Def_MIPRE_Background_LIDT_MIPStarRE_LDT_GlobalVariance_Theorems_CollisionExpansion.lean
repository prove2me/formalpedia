-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_CollisionExpansion
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_CollisionExpansion
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T03:18:03.337077+00:00
-- url     : https://prove2.me/theorems/41fa6d8f-d9fb-4d93-82f2-756e2dd0d0de
-- title:
--   Definitions of CollisionExpansion: Collision expansion and Schwartz-Zippel bounds This module contains the `generalizeB` theorem wrappers, finite…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.GlobalVariance.Theorems.CollisionExpansion` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Collision expansion and Schwartz-Zippel bounds. This module contains the `generalizeB` theorem wrappers, finite reparametrization and distribution bookkeeping, and the Schwartz-Zippel collision expansion that bounds the line-collision residual.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Definitions** (2): `MIPStarRE.LDT.GlobalVariance.axisParallelLinePointParamEquiv` (Reindex a line representative and affine parameter by the sampled point on that line, keeping the direction and parameter as auxiliary data.); `_private.MIPRE.Background.LIDT.MIPStarRE.LDT.GlobalVariance.Theorems.CollisionExpansion.0.MIPStarRE.LDT.GlobalVariance.axisParallelLineQuestionParameterEquiv` (The finite reparametrization of incident axis-parallel line questions by a line `ℓ` and affine parameter `t`, sending `(ℓ,t)` to `(ℓ,…).
--
--   **Embedded lemmas** (4): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `avgOver_axisParallelLinePointParam`, `generalizeBCollisionSeed_integrand`, `generalizeBLineCollisionTensorMass_sum_le_one`, `generalizeB_of_pointwise`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.GlobalVariance.Theorems.CollisionExpansion` (`MIPRE/Background/LIDT/MIPStarRE/LDT/GlobalVariance/Theorems/CollisionExpansion.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 50 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/GlobalVariance/Theorems/CollisionExpansion.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/GlobalVariance/Theorems/CollisionExpansion.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/GlobalVariance/Theorems/CollisionExpansion.lean (definition bundle: declarations the uploaded statements rest on);
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
import Theorems.Thm_MIPStarRE_LDT_GlobalVariance_avgOver_polynomialDistribution_le_of_pointwise
import Theorems.Thm_MIPStarRE_LDT_GlobalVariance_sddRel_unit_family_of_pointwise
import Theorems.Thm_MIPStarRE_LDT_Polynomial_restrictToAxisParallelLine_apply
import Theorems.Thm_MIPStarRE_LDT_SubMeas_outcome_le_one
import Theorems.Thm_MIPStarRE_LDT_SubMeas_total_nonneg
import Theorems.Thm_MIPStarRE_LDT_avgOver_congr
import Theorems.Thm_MIPStarRE_LDT_avgOver_uniform_equiv
import Theorems.Thm_MIPStarRE_LDT_avgOver_uniform_fst
import Theorems.Thm_MIPStarRE_LDT_ev_finset_sum
import Theorems.Thm_MIPStarRE_LDT_ev_mono
import Theorems.Thm_MIPStarRE_LDT_ev_sum
import Theorems.Thm_MIPStarRE_LDT_leftTensor_finset_sum
import Theorems.Thm_MIPStarRE_LDT_leftTensor_le_one
import Theorems.Thm_MIPStarRE_LDT_leftTensor_mul_rightTensor_eq_opTensor
import Theorems.Thm_MIPStarRE_LDT_opTensor_le_leftTensor
import Theorems.Thm_MIPStarRE_LDT_opTensor_sum_left_finset

attribute [simp] MIPStarRE.LDT.Polynomial.restrictToAxisParallelLine_apply

set_option backward.isDefEq.respectTransparency false

namespace MIPStarRE.LDT.GlobalVariance

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
open MIPStarRE.LDT.MakingMeasurementsProjective
open MIPStarRE.LDT.ExpansionHypercubeGraph
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! # Collision expansion and Schwartz-Zippel bounds

This module contains the `generalizeB` theorem wrappers, finite reparametrization
and distribution bookkeeping, and the Schwartz-Zippel collision expansion that
bounds the line-collision residual.
-/

lemma generalizeB_of_pointwise
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (ψbi : QuantumState (ι × ι))
    (hpoint :
      ∀ g : Polynomial params,
        generalizeBDeviationAtPolynomial params strategy ψbi G g ≤ generalizeBError params) :
    GeneralizeBStatement params strategy ψbi G := by
  refine
    { aggregateFamilyComparison := by
        exact sddRel_unit_family_of_pointwise ψbi
          (axisParallelLineQuestionDistribution params)
          (generalizeBLeftFamily params strategy G)
          (generalizeBRightFamily params strategy G)
          (fun qu g =>
            weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu)
          (fun qu g =>
            weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu)
          (by
            intro qu
            simp [generalizeBLeftFamily])
          (by
            intro qu
            simp [generalizeBRightFamily])
          (generalizeBError params) (by
            intro g
            simpa [generalizeBDeviationAtPolynomial] using hpoint g)
      pointwiseNormBound := hpoint
      averagedNormBound :=
        avgOver_polynomialDistribution_le_of_pointwise params
          (fun g => generalizeBDeviationAtPolynomial params strategy ψbi G g)
          (generalizeBError params) hpoint }

/-- The finite reparametrization of incident axis-parallel line questions by a
line `ℓ` and affine parameter `t`, sending `(ℓ,t)` to `(ℓ, ℓ(t))`. -/
noncomputable def axisParallelLineQuestionParameterEquiv (params : Parameters)
    [FieldModel params.q] :
    AxisParallelLine params × Fq params ≃
      {qu : AxisParallelLineQuestion params // pointOnLine (params := params) qu} where
  toFun := fun ℓt => ⟨(ℓt.1, ℓt.1.pointAt ℓt.2), ⟨ℓt.2, rfl⟩⟩
  invFun := fun qu => (qu.1.1, axisParallelLineQuestionParameter qu.1)
  left_inv := fun
    | ⟨ℓ, t⟩ => by
        simp [axisParallelLineQuestionParameter_pointAt]
  right_inv := fun
    | ⟨⟨ℓ, u⟩, ⟨t, ht⟩⟩ => by
        apply Subtype.ext
        dsimp only
        have hparam : axisParallelLineQuestionParameter (ℓ, u) = t := by
          calc
            axisParallelLineQuestionParameter (ℓ, u) =
                axisParallelLineQuestionParameter (ℓ, ℓ.pointAt t) := by rw [ht]
            _ = t := axisParallelLineQuestionParameter_pointAt ℓ t
        ext <;> simp [hparam, ht]

/-- Reindex a line representative and affine parameter by the sampled point on
that line, keeping the direction and parameter as auxiliary data.

This is the finite bookkeeping behind `expansion.tex`, lines 300--302: averaging
over a line representative `ℓ` and a parameter `t` is the same as averaging over
the sampled base point `u = ℓ(t)`, the direction, and the forgotten parameter. -/
noncomputable def axisParallelLinePointParamEquiv (params : Parameters)
    [FieldModel params.q] :
    AxisParallelLine params × Fq params ≃ AxisParallelTestSample params × Fq params where
  toFun := fun ℓt => ((ℓt.1.pointAt ℓt.2, ℓt.1.direction), ℓt.2)
  invFun := fun st =>
    (({ base := fun j => if j = st.1.2 then subCoord (st.1.1 j) st.2 else st.1.1 j,
        direction := st.1.2 } : AxisParallelLine params), st.2)
  left_inv := fun
    | ⟨⟨base, direction⟩, t⟩ => by
      simp only [Prod.mk.injEq, AxisParallelLine.mk.injEq, and_true]
      funext j
      by_cases hj : j = direction <;>
        simp [AxisParallelLine.pointAt, hj, subCoord_addCoord_right]
  right_inv := fun
    | ⟨⟨u, direction⟩, t⟩ => by
      simp only [Prod.mk.injEq, and_true]
      ext j
      by_cases hj : j = direction <;>
        simp [AxisParallelLine.pointAt, hj]

/-- Marginalizing the uniform line/parameter presentation to the sampled point
and direction gives the native axis-parallel base-point test distribution. -/
lemma avgOver_axisParallelLinePointParam
    (params : Parameters) [FieldModel params.q]
    (f : AxisParallelTestSample params → Error) :
    avgOver (uniformDistribution (AxisParallelLine params × Fq params))
      (fun ℓt => f (ℓt.1.pointAt ℓt.2, ℓt.1.direction)) =
    avgOver (uniformDistribution (AxisParallelTestSample params)) f := by
  let e := axisParallelLinePointParamEquiv params
  calc
    avgOver (uniformDistribution (AxisParallelLine params × Fq params))
        (fun ℓt => f (ℓt.1.pointAt ℓt.2, ℓt.1.direction))
      = avgOver (uniformDistribution (AxisParallelTestSample params × Fq params))
          (fun st => f ((e.symm st).1.pointAt (e.symm st).2, (e.symm st).1.direction)) := by
          exact avgOver_uniform_equiv (e := e)
            (f := fun ℓt : AxisParallelLine params × Fq params =>
              f (ℓt.1.pointAt ℓt.2, ℓt.1.direction))
    _ = avgOver (uniformDistribution (AxisParallelTestSample params × Fq params))
          (fun st => f st.1) := by
          apply avgOver_congr
          intro st
          have h := congrArg Prod.fst (e.right_inv st)
          exact congrArg f h
    _ = avgOver (uniformDistribution (AxisParallelTestSample params)) f :=
        avgOver_uniform_fst f

/-- Expanding the postprocessed collision event at the seeded question
`(ℓ, ℓ(t))` gives the line-answer sum from `expansion.tex`, lines 283--286. -/
lemma generalizeBCollisionSeed_integrand
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (ψbi : QuantumState (ι × ι))
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params)
    (ℓ : AxisParallelLine params) (t : Fq params) :
    ev ψbi (opTensor
        (generalizeBCollisionOperatorAtPolynomial params strategy g (ℓ, ℓ.pointAt t))
        (G.outcome g)) =
      ∑ f : AxisLinePolynomial params,
        (if f t = (Polynomial.restrictToAxisParallelLine params g ℓ) t ∧
            f.poly ≠ (Polynomial.restrictToAxisParallelLine params g ℓ).poly then
          (1 : Error)
        else 0) *
          ev ψbi (opTensor
            ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome f)
            (G.outcome g)) := by
  classical
  unfold generalizeBCollisionOperatorAtPolynomial generalizeBCollisionEventSubMeasAtPolynomial
    generalizeBCollisionEventProjMeasAtPolynomial
  simp only [ProjMeas.postprocess, postprocess, axisParallelLineQuestionParameter_pointAt,
    Polynomial.restrictToAxisParallelLine_apply]
  rw [opTensor_sum_left_finset]
  rw [ev_finset_sum]
  simp [Finset.sum_filter]

/-- The total tensor mass left after summing over line answers is at most one.

This is the normalization half of `expansion.tex`, lines 286--288: the
left-register line measurement sums to its total operator, the right-register
operator is the single submeasurement outcome `G_g ≤ 1`, and the strategy state
is normalized. -/
lemma generalizeBLineCollisionTensorMass_sum_le_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) (ℓ : AxisParallelLine params) :
    (∑ f : AxisLinePolynomial params,
      ev strategy.state (opTensor ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome f)
        (G.outcome g))) ≤ 1 := by
  let B := (strategy.axisParallelMeasurement ℓ).toSubMeas
  calc
    (∑ f : AxisLinePolynomial params,
      ev strategy.state (opTensor (B.outcome f) (G.outcome g)))
      = ev strategy.state (∑ f : AxisLinePolynomial params,
          opTensor (B.outcome f) (G.outcome g)) := by
          rw [ev_sum]
    _ = ev strategy.state (leftTensor (ι₂ := ι) B.total *
          rightTensor (ι₁ := ι) (G.outcome g)) := by
          congr 1
          calc
            (∑ f : AxisLinePolynomial params, opTensor (B.outcome f) (G.outcome g))
              = ∑ f : AxisLinePolynomial params,
                  leftTensor (ι₂ := ι) (B.outcome f) *
                    rightTensor (ι₁ := ι) (G.outcome g) := by
                    simp [leftTensor_mul_rightTensor_eq_opTensor]
            _ = (∑ f : AxisLinePolynomial params, leftTensor (ι₂ := ι) (B.outcome f)) *
                  rightTensor (ι₁ := ι) (G.outcome g) := by
                    rw [Finset.sum_mul]
            _ = leftTensor (ι₂ := ι) B.total * rightTensor (ι₁ := ι) (G.outcome g) := by
                    rw [leftTensor_finset_sum (ι₂ := ι) Finset.univ B.outcome]
                    rw [B.sum_eq_total]
    _ ≤ ev strategy.state (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
          apply ev_mono strategy.state _ _
          calc
            leftTensor (ι₂ := ι) B.total * rightTensor (ι₁ := ι) (G.outcome g)
              = opTensor B.total (G.outcome g) := by
                  rw [leftTensor_mul_rightTensor_eq_opTensor]
            _ ≤ leftTensor (ι₂ := ι) B.total :=
                  opTensor_le_leftTensor (SubMeas.total_nonneg B) (SubMeas.outcome_le_one G g)
            _ ≤ 1 := leftTensor_le_one (ι₂ := ι) B.total_le_one
    _ = 1 := ev_one_of_isNormalized strategy.state strategy.isNormalized

end MIPStarRE.LDT.GlobalVariance


