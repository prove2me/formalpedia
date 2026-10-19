-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep34AndTransfer_Selected
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep34AndTransfer_Selected
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T04:51:17.342084+00:00
-- url     : https://prove2.me/theorems/8a66a75b-0092-4b77-88cd-3ece4f884e41
-- title:
--   Definitions of Selected: Selected add-in-u Step 3/4 global-variance bounds Selected-family Cauchy--Schwarz estimates and factor bounds for the…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.SelfImprovement.Theorems.Results.AddInUStep34AndTransfer.Selected` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Selected add-in-u Step 3/4 global-variance bounds. Selected-family Cauchy--Schwarz estimates and factor bounds for the `Q₂ → Q₃` and `Q₃ → Q₄` add-in-u moves.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Embedded lemmas** (6): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `addInU_selected_cs_chain_self_energy_factor_le_one_at`, `addInU_selected_cs_chain_step34_variance_factor_le_globalVarianceDeviation_sum`, `addInU_selected_cs_chain_step3_factored_cs`, `addInU_selected_cs_chain_step4_factored_cs`, `addInU_selected_sandwich_tensor_if_sum_le`, `addInU_selected_weighted_cauchy_schwarz`.
--
--   The bundle holds no definition of its own: it carries the lemmas listed above, which later bundles and proofs import.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.SelfImprovement.Theorems.Results.AddInUStep34AndTransfer.Selected` (`MIPRE/Background/LIDT/MIPStarRE/LDT/SelfImprovement/Theorems/Results/AddInUStep34AndTransfer/Selected.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 83 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/SelfImprovement/Theorems/Results/AddInUStep34AndTransfer/Selected.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/SelfImprovement/Theorems/Results/AddInUStep34AndTransfer/Selected.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/SelfImprovement/Theorems/Results/AddInUStep34AndTransfer/Selected.lean (definition bundle: declarations the uploaded statements rest on);
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
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.Group.Invertible.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Prod
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
import Mathlib.Algebra.Module.Prod
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Module.Submodule.LinearMap
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
import Mathlib.Algebra.Notation.Prod
import Mathlib.Algebra.Opposites
import Mathlib.Algebra.Order.Archimedean.Basic
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
import Mathlib.Algebra.Ring.Basic
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
import Mathlib.Analysis.Convex.Cone.Closure
import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Real.Spectrum
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
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
import Mathlib.Data.Finset.Prod
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
import Mathlib.Data.FunLike.IsApply
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
import Mathlib.Data.SProd
import Mathlib.Data.Set.Basic
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
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
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
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Order.Filter.Extr
import Mathlib.Order.Filter.Tendsto
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
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
import Mathlib.Tactic.Linarith.Preprocessing
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
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Algebra.Star.Real
import Mathlib.Topology.Algebra.UniformMulAction
import Mathlib.Topology.Bases
import Mathlib.Topology.Basic
import Mathlib.Topology.Bornology.Basic
import Mathlib.Topology.Closure
import Mathlib.Topology.Constructions
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Continuous
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.EMetricSpace.Defs
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.Real
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Sequences
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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_CompletionTransfer
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_Triangles_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_PolynomialAgreement
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Operators
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Families
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Statements
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_SelfConsistency_DataProcessing
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Thresholds_Final
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperCompleteness_InputSdp
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperCompleteness_FiberBounds
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperCompleteness_Linearized
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Fourier
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_MatrixRealization_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_MatrixRealization_TraceForms
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Base
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_CanonicalPrimal
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical_Witness
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical_Saturated
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteConicDuality
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical_StrongDuality_Basic
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical_StrongDuality_Separation
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_SdpMatrixBridge
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Theorems_Foundations
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Theorems_Matrix
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Theorems_Results
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_Averaging
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_Statements
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_AlgebraicIdentity
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_CollisionExpansion
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_SelfConsistencyTransport_PointLine
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_TransportChain_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_SelfConsistencyTransportSum
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_PolynomialSumBounds
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperCompleteness_Bracketed
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUDiagonalAndDefs_Selection
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUDiagonalAndDefs_Residual
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUDiagonalAndDefs_ScalarChain
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep12_Algebra
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep12_Raw
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep12_Selected
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep34AndTransfer_Factored
import Theorems.Thm_MIPStarRE_LDT_ExpansionHypercubeGraph_avgOver_independentPointPair_eq_uniform_prod
import Theorems.Thm_MIPStarRE_LDT_Preliminaries_weightedFinsetCauchySchwarz_on_selectedSupport
import Theorems.Thm_MIPStarRE_LDT_SelfImprovement_addInU_selected_cs_chain_step3_diff_eq
import Theorems.Thm_MIPStarRE_LDT_SelfImprovement_addInU_selected_cs_chain_step4_diff_eq
import Theorems.Thm_MIPStarRE_LDT_SubMeas_outcome_hermitian
import Theorems.Thm_MIPStarRE_LDT_SubMeas_outcome_le_one
import Theorems.Thm_MIPStarRE_LDT_avgOver_congr
import Theorems.Thm_MIPStarRE_LDT_avgOver_mono
import Theorems.Thm_MIPStarRE_LDT_avgOver_sum
import Theorems.Thm_MIPStarRE_LDT_avgOver_uniform_le_const
import Theorems.Thm_MIPStarRE_LDT_ev_finset_sum
import Theorems.Thm_MIPStarRE_LDT_ev_mono
import Theorems.Thm_MIPStarRE_LDT_ev_opTensor_sandwich_abs_le_sqrt
import Theorems.Thm_MIPStarRE_LDT_ev_zero
import Theorems.Thm_MIPStarRE_LDT_opTensor_mono_left
import Theorems.Thm_MIPStarRE_LDT_opTensor_sum_left_univ
import Theorems.Thm_MIPStarRE_LDT_opTensor_sum_right_univ
import Theorems.Thm_MIPStarRE_LDT_rightTensor_le_one

set_option backward.isDefEq.respectTransparency false

/-!
# Selected add-in-u Step 3/4 global-variance bounds

Selected-family Cauchy--Schwarz estimates and factor bounds for the
`Q₂ → Q₃` and `Q₃ → Q₄` add-in-u moves.

## References

- `references/ldt-paper/self_improvement.tex` lines 299--340
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Selected-support weighted Cauchy--Schwarz for the add-in-`u` Step 3/4
summands.

The selected Step 3 and Step 4 estimates use the same finite inequality: the
summands are restricted to the selected pairs `S_u`, and are extended by zero
outside this support.  This helper fixes the distribution and the selected
support, leaving only the three summands and their pointwise estimates to be
specified by the two applications. -/
theorem addInU_selected_weighted_cauchy_schwarz
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (params : Parameters) [FieldModel params.q]
    (S : AddInUSelection params Outcome)
    (t x y : Point params × Point params → Outcome × Polynomial params → Error)
    (ht :
      ∀ uv ah, ah ∈ addInUSelectionPairs params S uv.1 →
        |t uv ah| ≤ Real.sqrt (x uv ah) * Real.sqrt (y uv ah))
    (hx : ∀ uv ah, ah ∈ addInUSelectionPairs params S uv.1 → 0 ≤ x uv ah)
    (hy : ∀ uv ah, ah ∈ addInUSelectionPairs params S uv.1 → 0 ≤ y uv ah) :
    |avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
      ∑ ah : Outcome × Polynomial params,
        if ah ∈ addInUSelectionPairs params S uv.1 then t uv ah else 0)| ≤
      Real.sqrt
        (avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
          ∑ ah : Outcome × Polynomial params,
            if ah ∈ addInUSelectionPairs params S uv.1 then x uv ah else 0)) *
      Real.sqrt
        (avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
          ∑ ah : Outcome × Polynomial params,
            if ah ∈ addInUSelectionPairs params S uv.1 then y uv ah else 0)) := by
  classical
  exact
    MIPStarRE.LDT.Preliminaries.weightedFinsetCauchySchwarz_on_selectedSupport
      (𝒟 := uniformDistribution (Point params × Point params))
      (selected := fun uv ah => ah ∈ addInUSelectionPairs params S uv.1)
      (t := t) (x := x) (y := y) ht hx hy

/-- Selected factored Cauchy--Schwarz bound for the `Q₂ → Q₃` add-in-`u` step.

This is the selection-parametrized analogue of
`add_in_u_cs_chain_q2_q3_factored_cs`.  The summation is over all pairs
`(o,h)`, with the terms outside the selected set `S_u` set to zero; this form is
convenient for the finite Cauchy--Schwarz lemma and is equivalent to the
fiberwise selected sum appearing in the paper. -/
theorem addInU_selected_cs_chain_step3_factored_cs
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome) :
    |addInUSelectedCSChainQ2 params strategy M T S -
        addInUSelectedCSChainQ3 params strategy M T S| ≤
      Real.sqrt
        (avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
          ∑ ah : Outcome × Polynomial params,
            if ah ∈ addInUSelectionPairs params S uv.1 then
              let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
              let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
              let Moh := (M uv.1).outcome ah.1
              ev strategy.state
                (opTensor ((Av - Au) * Moh * (Av - Au)) (T.outcome ah.2))
            else 0)) *
      Real.sqrt
        (avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
          ∑ ah : Outcome × Polynomial params,
            if ah ∈ addInUSelectionPairs params S uv.1 then
              let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
              let Moh := (M uv.1).outcome ah.1
              ev strategy.state
                (opTensor (Av * Moh * Av) (T.outcome ah.2))
            else 0)) := by
  classical
  rw [addInU_selected_cs_chain_step3_diff_eq params strategy M T S]
  simpa using
    addInU_selected_weighted_cauchy_schwarz (Outcome := Outcome) params S
      (t := fun uv ah =>
        let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
        let Moh := (M uv.1).outcome ah.1
        ev strategy.state (opTensor ((Av - Au) * Moh * Av) (T.outcome ah.2)))
      (x := fun uv ah =>
        let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
        let Moh := (M uv.1).outcome ah.1
        ev strategy.state
          (opTensor ((Av - Au) * Moh * (Av - Au)) (T.outcome ah.2)))
      (y := fun uv ah =>
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
        let Moh := (M uv.1).outcome ah.1
        ev strategy.state (opTensor (Av * Moh * Av) (T.outcome ah.2)))
      (by
        intro uv ah _hmem
        set Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
        set Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
        set Moh := (M uv.1).outcome ah.1
        have hMoh_pos : 0 ≤ Moh := (M uv.1).outcome_pos ah.1
        have hTh_pos : 0 ≤ T.outcome ah.2 := T.outcome_pos ah.2
        have hAu_herm : Auᴴ = Au :=
          SubMeas.outcome_hermitian (strategy.pointMeasurement uv.1).toSubMeas
            (ah.2 uv.1)
        have hAv_herm : Avᴴ = Av :=
          SubMeas.outcome_hermitian (strategy.pointMeasurement uv.2).toSubMeas
            (ah.2 uv.2)
        have hX_herm : (Av - Au)ᴴ = Av - Au := by
          rw [Matrix.conjTranspose_sub, hAu_herm, hAv_herm]
        have hsandwich :=
          ev_opTensor_sandwich_abs_le_sqrt strategy.state (Av - Au) Av Moh
            (T.outcome ah.2) hMoh_pos hTh_pos
        simpa only [hX_herm, hAv_herm] using hsandwich)
      (by
        intro uv ah _hmem
        set Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
        set Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
        set Moh := (M uv.1).outcome ah.1
        have hMoh_pos : 0 ≤ Moh := (M uv.1).outcome_pos ah.1
        have hTh_pos : 0 ≤ T.outcome ah.2 := T.outcome_pos ah.2
        have hAu_herm : Auᴴ = Au :=
          SubMeas.outcome_hermitian (strategy.pointMeasurement uv.1).toSubMeas
            (ah.2 uv.1)
        have hAv_herm : Avᴴ = Av :=
          SubMeas.outcome_hermitian (strategy.pointMeasurement uv.2).toSubMeas
            (ah.2 uv.2)
        have hX_herm : (Av - Au)ᴴ = Av - Au := by
          rw [Matrix.conjTranspose_sub, hAu_herm, hAv_herm]
        have hXMohX_pos : 0 ≤ (Av - Au) * Moh * (Av - Au) := by
          have this : 0 ≤ (Av - Au)ᴴ * Moh * (Av - Au) := by
            simpa [Matrix.star_eq_conjTranspose] using
              star_left_conjugate_nonneg hMoh_pos (Av - Au)
          rwa [hX_herm] at this
        exact ev_nonneg_of_psd strategy.state _
          (opTensor_nonneg hXMohX_pos hTh_pos))
      (by
        intro uv ah _hmem
        set Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
        set Moh := (M uv.1).outcome ah.1
        have hMoh_pos : 0 ≤ Moh := (M uv.1).outcome_pos ah.1
        have hTh_pos : 0 ≤ T.outcome ah.2 := T.outcome_pos ah.2
        have hAv_herm : Avᴴ = Av :=
          SubMeas.outcome_hermitian (strategy.pointMeasurement uv.2).toSubMeas
            (ah.2 uv.2)
        have hAvMohAv_pos : 0 ≤ Av * Moh * Av := by
          have this : 0 ≤ Avᴴ * Moh * Av := by
            simpa [Matrix.star_eq_conjTranspose] using
              star_left_conjugate_nonneg hMoh_pos Av
          rwa [hAv_herm] at this
        exact ev_nonneg_of_psd strategy.state _
          (opTensor_nonneg hAvMohAv_pos hTh_pos))

/-- Selected factored Cauchy--Schwarz bound for the `Q₃ → Q₄` add-in-`u` step.

This is the selection-parametrized analogue of
`add_in_u_cs_chain_q3_q4_factored_cs`; as in
`addInU_selected_cs_chain_step3_factored_cs`, terms outside the selected set
are represented by zeros in the finite Cauchy--Schwarz sum. -/
theorem addInU_selected_cs_chain_step4_factored_cs
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome) :
    |addInUSelectedCSChainQ3 params strategy M T S -
        addInUSelectedCSChainQ4 params strategy M T S| ≤
      Real.sqrt
        (avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
          ∑ ah : Outcome × Polynomial params,
            if ah ∈ addInUSelectionPairs params S uv.1 then
              let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
              let Moh := (M uv.1).outcome ah.1
              ev strategy.state (opTensor (Au * Moh * Au) (T.outcome ah.2))
            else 0)) *
      Real.sqrt
        (avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
          ∑ ah : Outcome × Polynomial params,
            if ah ∈ addInUSelectionPairs params S uv.1 then
              let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
              let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
              let Moh := (M uv.1).outcome ah.1
              ev strategy.state
                (opTensor ((Av - Au) * Moh * (Av - Au)) (T.outcome ah.2))
            else 0)) := by
  classical
  rw [addInU_selected_cs_chain_step4_diff_eq params strategy M T S]
  simpa using
    addInU_selected_weighted_cauchy_schwarz (Outcome := Outcome) params S
      (t := fun uv ah =>
        let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
        let Moh := (M uv.1).outcome ah.1
        ev strategy.state (opTensor (Au * Moh * (Av - Au)) (T.outcome ah.2)))
      (x := fun uv ah =>
        let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
        let Moh := (M uv.1).outcome ah.1
        ev strategy.state (opTensor (Au * Moh * Au) (T.outcome ah.2)))
      (y := fun uv ah =>
        let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
        let Moh := (M uv.1).outcome ah.1
        ev strategy.state
          (opTensor ((Av - Au) * Moh * (Av - Au)) (T.outcome ah.2)))
      (by
        intro uv ah _hmem
        set Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
        set Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
        set Moh := (M uv.1).outcome ah.1
        have hMoh_pos : 0 ≤ Moh := (M uv.1).outcome_pos ah.1
        have hTh_pos : 0 ≤ T.outcome ah.2 := T.outcome_pos ah.2
        have hAu_herm : Auᴴ = Au :=
          SubMeas.outcome_hermitian (strategy.pointMeasurement uv.1).toSubMeas
            (ah.2 uv.1)
        have hAv_herm : Avᴴ = Av :=
          SubMeas.outcome_hermitian (strategy.pointMeasurement uv.2).toSubMeas
            (ah.2 uv.2)
        have hY_herm : (Av - Au)ᴴ = Av - Au := by
          rw [Matrix.conjTranspose_sub, hAu_herm, hAv_herm]
        have hsandwich :=
          ev_opTensor_sandwich_abs_le_sqrt strategy.state Au (Av - Au) Moh
            (T.outcome ah.2) hMoh_pos hTh_pos
        simpa only [hAu_herm, hY_herm] using hsandwich)
      (by
        intro uv ah _hmem
        set Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
        set Moh := (M uv.1).outcome ah.1
        have hMoh_pos : 0 ≤ Moh := (M uv.1).outcome_pos ah.1
        have hTh_pos : 0 ≤ T.outcome ah.2 := T.outcome_pos ah.2
        have hAu_herm : Auᴴ = Au :=
          SubMeas.outcome_hermitian (strategy.pointMeasurement uv.1).toSubMeas
            (ah.2 uv.1)
        have hAuMohAu_pos : 0 ≤ Au * Moh * Au := by
          have this : 0 ≤ Auᴴ * Moh * Au := by
            simpa [Matrix.star_eq_conjTranspose] using
              star_left_conjugate_nonneg hMoh_pos Au
          rwa [hAu_herm] at this
        exact ev_nonneg_of_psd strategy.state _
          (opTensor_nonneg hAuMohAu_pos hTh_pos))
      (by
        intro uv ah _hmem
        set Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
        set Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
        set Moh := (M uv.1).outcome ah.1
        have hMoh_pos : 0 ≤ Moh := (M uv.1).outcome_pos ah.1
        have hTh_pos : 0 ≤ T.outcome ah.2 := T.outcome_pos ah.2
        have hAu_herm : Auᴴ = Au :=
          SubMeas.outcome_hermitian (strategy.pointMeasurement uv.1).toSubMeas
            (ah.2 uv.1)
        have hAv_herm : Avᴴ = Av :=
          SubMeas.outcome_hermitian (strategy.pointMeasurement uv.2).toSubMeas
            (ah.2 uv.2)
        have hY_herm : (Av - Au)ᴴ = Av - Au := by
          rw [Matrix.conjTranspose_sub, hAu_herm, hAv_herm]
        have hYMohY_pos : 0 ≤ (Av - Au) * Moh * (Av - Au) := by
          have this : 0 ≤ (Av - Au)ᴴ * Moh * (Av - Au) := by
            simpa [Matrix.star_eq_conjTranspose] using
              star_left_conjugate_nonneg hMoh_pos (Av - Au)
          rwa [hY_herm] at this
        exact ev_nonneg_of_psd strategy.state _
          (opTensor_nonneg hYMohY_pos hTh_pos))

/-- A selected sandwich tensor sum is bounded by replacing the selected
submeasurement mass with the identity.

For a fixed point `u`, the selected pairs are a subcollection of
`Outcome × Polynomial params`.  Summing over all pairs, the `Outcome`-mass
collapses to `(M u).total`, and the submeasurement inequality
`(M u).total ≤ I` gives the displayed upper bound. -/
lemma addInU_selected_sandwich_tensor_if_sum_le
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (params : Parameters) [FieldModel params.q]
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome)
    (u : Point params)
    (X : Polynomial params → MIPStarRE.Quantum.Op ι)
    (hX_herm : ∀ h : Polynomial params, (X h)ᴴ = X h) :
    (∑ ah : Outcome × Polynomial params,
      if ah ∈ addInUSelectionPairs params S u then
        opTensor (X ah.2 * (M u).outcome ah.1 * X ah.2) (T.outcome ah.2)
      else 0) ≤
      ∑ h : Polynomial params, opTensor (X h * X h) (T.outcome h) := by
  classical
  let s := addInUSelectionPairs params S u
  let f : Outcome × Polynomial params → MIPStarRE.Quantum.Op (ι × ι) := fun ah =>
    opTensor (X ah.2 * (M u).outcome ah.1 * X ah.2) (T.outcome ah.2)
  have hf_nonneg : ∀ ah : Outcome × Polynomial params, 0 ≤ f ah := by
    intro ah
    have hM_pos : 0 ≤ (M u).outcome ah.1 := (M u).outcome_pos ah.1
    have hT_pos : 0 ≤ T.outcome ah.2 := T.outcome_pos ah.2
    have hleft_pos : 0 ≤ X ah.2 * (M u).outcome ah.1 * X ah.2 := by
      have this : 0 ≤ (X ah.2)ᴴ * (M u).outcome ah.1 * X ah.2 := by
        simpa [Matrix.star_eq_conjTranspose] using
          star_left_conjugate_nonneg hM_pos (X ah.2)
      rwa [hX_herm ah.2] at this
    exact opTensor_nonneg hleft_pos hT_pos
  have hif_eq :
      (∑ ah : Outcome × Polynomial params,
        if ah ∈ addInUSelectionPairs params S u then f ah else 0) =
        ∑ ah ∈ s, f ah := by
    simp [s]
  have hselected_le_univ :
      ∑ ah ∈ s, f ah ≤ ∑ ah : Outcome × Polynomial params, f ah :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (by
        intro ah _
        exact Finset.mem_univ ah)
      (by
        intro ah _ _
        exact hf_nonneg ah)
  have huniv_eq :
      (∑ ah : Outcome × Polynomial params, f ah) =
        ∑ h : Polynomial params,
          opTensor (X h * (M u).total * X h) (T.outcome h) := by
    calc
      (∑ ah : Outcome × Polynomial params, f ah)
          = ∑ o : Outcome, ∑ h : Polynomial params,
              opTensor (X h * (M u).outcome o * X h) (T.outcome h) := by
              rw [Fintype.sum_prod_type]
      _ = ∑ h : Polynomial params, ∑ o : Outcome,
            opTensor (X h * (M u).outcome o * X h) (T.outcome h) := by
            rw [Finset.sum_comm]
      _ = ∑ h : Polynomial params,
            opTensor (X h * (M u).total * X h) (T.outcome h) := by
            refine Finset.sum_congr rfl ?_
            intro h _
            calc
              ∑ o : Outcome,
                  opTensor (X h * (M u).outcome o * X h) (T.outcome h)
                  = opTensor
                      (∑ o : Outcome, X h * (M u).outcome o * X h)
                      (T.outcome h) := by
                    rw [opTensor_sum_left_univ]
              _ = opTensor (X h * (M u).total * X h) (T.outcome h) := by
                    congr 1
                    rw [← (M u).sum_eq_total, Finset.mul_sum, Finset.sum_mul]
  have htotal_le :
      ∑ h : Polynomial params,
          opTensor (X h * (M u).total * X h) (T.outcome h) ≤
        ∑ h : Polynomial params, opTensor (X h * X h) (T.outcome h) := by
    refine Finset.sum_le_sum ?_
    intro h _
    have hleft_le : X h * (M u).total * X h ≤ X h * 1 * X h :=
      IsSelfAdjoint.conjugate_le_conjugate (M u).total_le_one (hX_herm h)
    simpa using opTensor_mono_left hleft_le (T.outcome_pos h)
  calc
    (∑ ah : Outcome × Polynomial params,
      if ah ∈ addInUSelectionPairs params S u then
        opTensor (X ah.2 * (M u).outcome ah.1 * X ah.2) (T.outcome ah.2)
      else 0)
        = ∑ ah ∈ s, f ah := hif_eq
    _ ≤ ∑ ah : Outcome × Polynomial params, f ah := hselected_le_univ
    _ = ∑ h : Polynomial params,
          opTensor (X h * (M u).total * X h) (T.outcome h) := huniv_eq
    _ ≤ ∑ h : Polynomial params, opTensor (X h * X h) (T.outcome h) := htotal_le

lemma addInU_selected_cs_chain_self_energy_factor_le_one_at
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome)
    (p : Point params × Point params → Point params) :
    avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
      ∑ ah : Outcome × Polynomial params,
        if ah ∈ addInUSelectionPairs params S uv.1 then
          let A := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 (p uv)
          let Moh := (M uv.1).outcome ah.1
          ev strategy.state (opTensor (A * Moh * A) (T.outcome ah.2))
        else 0) ≤ 1 := by
  classical
  have hpointwise : ∀ uv : Point params × Point params,
      (∑ ah : Outcome × Polynomial params,
        if ah ∈ addInUSelectionPairs params S uv.1 then
          let A := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 (p uv)
          let Moh := (M uv.1).outcome ah.1
          ev strategy.state (opTensor (A * Moh * A) (T.outcome ah.2))
        else 0) ≤ 1 := by
    intro uv
    let X : Polynomial params → MIPStarRE.Quantum.Op ι :=
      fun h => pointConditionedOutcomeOperatorAtPolynomial params strategy h (p uv)
    have hX_herm : ∀ h : Polynomial params, (X h)ᴴ = X h := by
      intro h
      exact SubMeas.outcome_hermitian (strategy.pointMeasurement (p uv)).toSubMeas
        (h (p uv))
    have hsum_le :
        (∑ ah : Outcome × Polynomial params,
          if ah ∈ addInUSelectionPairs params S uv.1 then
            opTensor (X ah.2 * (M uv.1).outcome ah.1 * X ah.2) (T.outcome ah.2)
          else 0) ≤
        ∑ h : Polynomial params, opTensor (X h * X h) (T.outcome h) :=
      addInU_selected_sandwich_tensor_if_sum_le params M T S uv.1 X hX_herm
    have hright_le_one :
        (∑ h : Polynomial params, opTensor (X h * X h) (T.outcome h)) ≤
          (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
      calc
        ∑ h : Polynomial params, opTensor (X h * X h) (T.outcome h)
            = ∑ h : Polynomial params, opTensor (X h) (T.outcome h) := by
                refine Finset.sum_congr rfl ?_
                intro h _
                have hproj : X h * X h = X h := by
                  dsimp [X, pointConditionedOutcomeOperatorAtPolynomial]
                  exact (strategy.pointMeasurement (p uv)).proj (h (p uv))
                rw [hproj]
        _ ≤ ∑ h : Polynomial params,
              opTensor (1 : MIPStarRE.Quantum.Op ι) (T.outcome h) := by
              refine Finset.sum_le_sum ?_
              intro h _
              exact opTensor_mono_left
                ((strategy.pointMeasurement (p uv)).toSubMeas.outcome_le_one (h (p uv)))
                (T.outcome_pos h)
        _ = rightTensor (ι₁ := ι) T.total := by
              rw [← T.sum_eq_total, ← opTensor_sum_right_univ]
        _ ≤ 1 := rightTensor_le_one (ι₁ := ι) T.total_le_one
    have hop_le :
        (∑ ah : Outcome × Polynomial params,
          if ah ∈ addInUSelectionPairs params S uv.1 then
            let A := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 (p uv)
            let Moh := (M uv.1).outcome ah.1
            opTensor (A * Moh * A) (T.outcome ah.2)
          else 0) ≤ 1 := by
      simpa [X] using le_trans hsum_le hright_le_one
    calc
      (∑ ah : Outcome × Polynomial params,
        if ah ∈ addInUSelectionPairs params S uv.1 then
          let A := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 (p uv)
          let Moh := (M uv.1).outcome ah.1
          ev strategy.state (opTensor (A * Moh * A) (T.outcome ah.2))
        else 0)
          = ev strategy.state
              (∑ ah : Outcome × Polynomial params,
                if ah ∈ addInUSelectionPairs params S uv.1 then
                  let A := pointConditionedOutcomeOperatorAtPolynomial
                    params strategy ah.2 (p uv)
                  let Moh := (M uv.1).outcome ah.1
                  opTensor (A * Moh * A) (T.outcome ah.2)
                else 0) := by
              rw [ev_finset_sum]
              refine Finset.sum_congr rfl ?_
              intro ah _
              by_cases hmem : ah ∈ addInUSelectionPairs params S uv.1
              · simp [hmem]
              · simp [hmem, ev_zero]
      _ ≤ ev strategy.state (1 : MIPStarRE.Quantum.Op (ι × ι)) :=
            ev_mono strategy.state _ _ hop_le
      _ = 1 := ev_one_of_isNormalized strategy.state strategy.isNormalized
  exact avgOver_uniform_le_const _ 1 hpointwise

/-- The selected Step 3/4 variance factor is bounded by the summed
global-variance deviation.

The selected middle operators form a submeasurement after summing over their
outcome coordinate, so the selected sandwich is dominated by the square of
`A^v_{h(v)} - A^u_{h(u)}`.  Averaging over independent points identifies the
result with the global-variance deviation sum. -/
lemma addInU_selected_cs_chain_step34_variance_factor_le_globalVarianceDeviation_sum
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome) :
    avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
      ∑ ah : Outcome × Polynomial params,
        if ah ∈ addInUSelectionPairs params S uv.1 then
          let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
          let Moh := (M uv.1).outcome ah.1
          ev strategy.state
            (opTensor ((Av - Au) * Moh * (Av - Au)) (T.outcome ah.2))
        else 0) ≤
      ∑ g : Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy strategy.state T g := by
  classical
  let varianceTerm : Point params × Point params → Error := fun uv =>
    ∑ ah : Outcome × Polynomial params,
      if ah ∈ addInUSelectionPairs params S uv.1 then
        let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
        let Moh := (M uv.1).outcome ah.1
        ev strategy.state
          (opTensor ((Av - Au) * Moh * (Av - Au)) (T.outcome ah.2))
      else 0
  let squaredTerm : Point params × Point params → Polynomial params → Error :=
    fun uv h =>
      let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
      let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
      ev strategy.state (opTensor (((Au - Av)ᴴ) * (Au - Av)) (T.outcome h))
  have hpointwise : ∀ uv : Point params × Point params,
      varianceTerm uv ≤ ∑ h : Polynomial params, squaredTerm uv h := by
    intro uv
    let X : Polynomial params → MIPStarRE.Quantum.Op ι := fun h =>
      pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2 -
        pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
    have hX_herm : ∀ h : Polynomial params, (X h)ᴴ = X h := by
      intro h
      have hAu_herm :
          (pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1)ᴴ =
            pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1 :=
        SubMeas.outcome_hermitian (strategy.pointMeasurement uv.1).toSubMeas (h uv.1)
      have hAv_herm :
          (pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2)ᴴ =
            pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2 :=
        SubMeas.outcome_hermitian (strategy.pointMeasurement uv.2).toSubMeas (h uv.2)
      dsimp [X]
      rw [Matrix.conjTranspose_sub, hAv_herm, hAu_herm]
    have hop_le :
        (∑ ah : Outcome × Polynomial params,
          if ah ∈ addInUSelectionPairs params S uv.1 then
            opTensor (X ah.2 * (M uv.1).outcome ah.1 * X ah.2) (T.outcome ah.2)
          else 0) ≤
        ∑ h : Polynomial params, opTensor (X h * X h) (T.outcome h) :=
      addInU_selected_sandwich_tensor_if_sum_le params M T S uv.1 X hX_herm
    have hoperator_to_squared :
        (∑ h : Polynomial params, opTensor (X h * X h) (T.outcome h)) =
          ∑ h : Polynomial params,
            let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
            let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
            opTensor (((Au - Av)ᴴ) * (Au - Av)) (T.outcome h) := by
      refine Finset.sum_congr rfl ?_
      intro h _
      set Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
      set Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
      have hAu_herm : Auᴴ = Au :=
        SubMeas.outcome_hermitian (strategy.pointMeasurement uv.1).toSubMeas (h uv.1)
      have hAv_herm : Avᴴ = Av :=
        SubMeas.outcome_hermitian (strategy.pointMeasurement uv.2).toSubMeas (h uv.2)
      have hsq : (Av - Au) * (Av - Au) = ((Au - Av)ᴴ) * (Au - Av) := by
        rw [Matrix.conjTranspose_sub, hAu_herm, hAv_herm]
        noncomm_ring
      simpa [X, Au, Av] using congrArg (fun Z => opTensor Z (T.outcome h)) hsq
    calc
      varianceTerm uv
          = ev strategy.state
              (∑ ah : Outcome × Polynomial params,
                if ah ∈ addInUSelectionPairs params S uv.1 then
                  let Au := pointConditionedOutcomeOperatorAtPolynomial
                    params strategy ah.2 uv.1
                  let Av := pointConditionedOutcomeOperatorAtPolynomial
                    params strategy ah.2 uv.2
                  let Moh := (M uv.1).outcome ah.1
                  opTensor ((Av - Au) * Moh * (Av - Au)) (T.outcome ah.2)
                else 0) := by
              dsimp [varianceTerm]
              rw [ev_finset_sum]
              refine Finset.sum_congr rfl ?_
              intro ah _
              by_cases hmem : ah ∈ addInUSelectionPairs params S uv.1
              · simp [hmem]
              · simp [hmem, ev_zero]
      _ ≤ ev strategy.state (∑ h : Polynomial params,
              opTensor (X h * X h) (T.outcome h)) :=
            ev_mono strategy.state _ _ (by simpa [X] using hop_le)
      _ = ev strategy.state (∑ h : Polynomial params,
              let Au := pointConditionedOutcomeOperatorAtPolynomial
                params strategy h uv.1
              let Av := pointConditionedOutcomeOperatorAtPolynomial
                params strategy h uv.2
              opTensor (((Au - Av)ᴴ) * (Au - Av)) (T.outcome h)) := by
            rw [hoperator_to_squared]
      _ = ∑ h : Polynomial params, squaredTerm uv h := by
            rw [ev_finset_sum]
  have hvariance_le_squared :
      avgOver (uniformDistribution (Point params × Point params)) varianceTerm ≤
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ h : Polynomial params, squaredTerm uv h) := by
    refine avgOver_mono _ _ _ ?_
    intro uv
    exact hpointwise uv
  have hsquared_eq :
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ h : Polynomial params, squaredTerm uv h) =
      ∑ h : Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy strategy.state T h := by
    rw [avgOver_sum]
    refine Finset.sum_congr rfl ?_
    intro h _
    unfold globalVarianceDeviationAtPolynomial
    rw [avgOver_independentPointPair_eq_uniform_prod]
    refine avgOver_congr _ _ _ ?_
    intro uv
    simp only [squaredTerm]
    rw [← weightedPointConditionedOperator_sq]
  calc
    avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
      ∑ ah : Outcome × Polynomial params,
        if ah ∈ addInUSelectionPairs params S uv.1 then
          let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
          let Moh := (M uv.1).outcome ah.1
          ev strategy.state
            (opTensor ((Av - Au) * Moh * (Av - Au)) (T.outcome ah.2))
        else 0)
        = avgOver (uniformDistribution (Point params × Point params)) varianceTerm := by
            try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal
    _ ≤ avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
          ∑ h : Polynomial params, squaredTerm uv h) := hvariance_le_squared
    _ = ∑ g : Polynomial params,
          globalVarianceDeviationAtPolynomial params strategy strategy.state T g := hsquared_eq

end MIPStarRE.LDT.SelfImprovement


