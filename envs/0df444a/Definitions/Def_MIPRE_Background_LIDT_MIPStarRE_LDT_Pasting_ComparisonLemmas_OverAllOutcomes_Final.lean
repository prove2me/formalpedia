-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_OverAllOutcomes_Final
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_OverAllOutcomes_Final
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T07:09:22.479136+00:00
-- url     : https://prove2.me/theorems/4c5fc005-10fc-4235-98c4-38e63ddeaf70
-- title:
--   Definitions of Final: Section 12 pasting: over all outcomes — Schwartz–Zippel bounds and final assembly Schwartz–Zippel aggregation, the…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Pasting.ComparisonLemmas.OverAllOutcomes.Final` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Section 12 pasting: over all outcomes — Schwartz–Zippel bounds and final assembly. Schwartz–Zippel aggregation, the line-consistent indicator bound, and the final chained assembly of `lem:over-all-outcomes`.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Embedded lemmas** (8): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `avgOver_subMeasMass_restrict_liftLeft_eq_sum_coeff`, `lineConsistentIndicatorLocal_avg_le_mdq`, `lineConsistentIndicator_probability_le_mdq`, `overAllOutcomes_distinct_lineConsistent_indicator_mass_le_mdq`, `overAllOutcomes_distinct_nonglobal_mass_bound`, `overAllOutcomes_distinct_nonglobal_mass_le_bad_line_mass_add_mdq`, `overAllOutcomes_of_reverse_mass_bound`, `overAllOutcomes_reverse_mass_bound_of_nonglobal_mass_bound`.
--
--   The bundle holds no definition of its own: it carries the lemmas listed above, which later bundles and proofs import.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Pasting.ComparisonLemmas.OverAllOutcomes.Final` (`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/ComparisonLemmas/OverAllOutcomes/Final.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 103 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/ComparisonLemmas/OverAllOutcomes/Final.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Pasting/ComparisonLemmas/OverAllOutcomes/Final.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/ComparisonLemmas/OverAllOutcomes/Final.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.NonUnitalHom
import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.BigOperators.Intervals
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
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Invertible.Basic
import Mathlib.Algebra.Group.Invertible.Defs
import Mathlib.Algebra.Group.Nat.Defs
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
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Opposites
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
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
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.NatCast
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
import Mathlib.Algebra.Order.Nonneg.Basic
import Mathlib.Algebra.Order.Nonneg.Module
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Algebra.Order.Sub.Defs
import Mathlib.Algebra.Order.SuccPred
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.CStarAlgebra.Module.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Convex.Cone.Basic
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
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
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
import Mathlib.Data.Fin.Tuple.Basic
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
import Mathlib.Data.Finset.Lattice.Lemmas
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.CardEmbedding
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
import Mathlib.Data.List.Nodup
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Multiset.Defs
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Commute
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
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
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Operations
import Mathlib.Data.SetLike.Basic
import Mathlib.Data.Subtype
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Trace
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
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Set.Defs
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
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Push
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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MainInductionStep_Defs
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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_Triangles_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_LinePolynomialEmbedding
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyPolynomialFamilies
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Defs_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Defs_Stability
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Defs_Normalization
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Products
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_CommutativityPoints_Approximation
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_EvaluatedSliceBounds_PhaseOneThree
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_EvaluatedSliceCommutation_Averages
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Transport_EvaluationSpecialization
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Transport_Pullback
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_PolynomialAgreement
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Averages
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Marginalization_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Marginalization_Y
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Normalization
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Bridges_Closeness
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Bridges_QSDD
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_ZeroBounds
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Main_Auxiliary_HEvalTransport
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Main_Auxiliary_ScalarMarginalization
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_CommutativityPoints_SharedHelpers_SharedLine
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_CommutativityPoints_BridgeTheorems_DropBridges
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_GCommStability_Scalar_RawSecond
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_PaperChainPhaseFive
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_GCommStability_Scalar_First
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_ProcessedG_PhaseTwo
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_ProcessedG_MainChain
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Defs_Tuples
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Sandwich_Switcheroo
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Sandwich_GHatSandwich
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Sandwich_PastedFamilies
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Statements
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_SwitcherooSetup_Centers
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_SwitcherooSetup_Terms
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_SwitcherooContraction_Split
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_SwitcherooContraction_ScalarTerms
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_SwitcherooCompletion
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_CommutingWithG_Complete
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_GHatFacts
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_Setup_Definitions
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_Setup_StepLemmas_Split
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_Base
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_Lifting
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_Chain
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_FlatChain
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_BackChain
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_EndpointEquivs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Core_LdGbcon
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_Endpoint
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_PrefixMoved
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_CSSetup
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LineInterpolation_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LineInterpolation_BadLine
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LineInterpolation_BadMass
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_HBConsistency
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_HAConsistency
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_OverAllOutcomes_ErrorAndMass
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_OverAllOutcomes_NonglobalDecomposition
import Theorems.Thm_MIPStarRE_LDT_Pasting_avgOver_distinct_eligibleMass_eq_global_add_nonglobal
import Theorems.Thm_MIPStarRE_LDT_Pasting_avgOver_uniform_eligibleMass_le_distinct_add_dnoteq
import Theorems.Thm_MIPStarRE_LDT_Pasting_distinctTupleDistribution_weight_sum_le_one
import Theorems.Thm_MIPStarRE_LDT_Pasting_dnoteq_term_le_overAllOutcomesError
import Theorems.Thm_MIPStarRE_LDT_Pasting_hBConsistencyError_add_mdq_add_dnoteq_le_overAllOutcomesError
import Theorems.Thm_MIPStarRE_LDT_Pasting_lineConsistentNonglobalMass_le_indicatorMass
import Theorems.Thm_MIPStarRE_LDT_Pasting_nonglobal_gives_slice_mismatch_against_interpolant
import Theorems.Thm_MIPStarRE_LDT_Pasting_overAllOutcomesExpansionMass_eq_avg_uniform_eligible
import Theorems.Thm_MIPStarRE_LDT_Pasting_overAllOutcomesPastedMass_eq_avg_distinct_global
import Theorems.Thm_MIPStarRE_LDT_Pasting_overAllOutcomes_distinct_bad_line_mass_le_hBConsistencyError
import Theorems.Thm_MIPStarRE_LDT_Pasting_overAllOutcomes_distinct_nonglobal_mass_le_bad_line_mass_add_lineConsistent
import Theorems.Thm_MIPStarRE_LDT_Pasting_overAllOutcomes_pasted_sub_expansion_le_dnoteq
import Theorems.Thm_MIPStarRE_LDT_Pasting_restrictToVerticalLine_eval_eq_restrictAtHeight_eval
import Theorems.Thm_MIPStarRE_LDT_Pasting_tupleInterpolatedVerticalLine_eq_of_no_supported_mismatch
import Theorems.Thm_MIPStarRE_LDT_Polynomial_restrictToAxisParallelLine_apply
import Theorems.Thm_MIPStarRE_LDT_Preliminaries_polynomialAgreement_avg_le_mdq
import Theorems.Thm_MIPStarRE_LDT_avgOver_comm
import Theorems.Thm_MIPStarRE_LDT_avgOver_congr
import Theorems.Thm_MIPStarRE_LDT_avgOver_mono
import Theorems.Thm_MIPStarRE_LDT_avgOver_mono_on_support
import Theorems.Thm_MIPStarRE_LDT_avgOver_mul_const
import Theorems.Thm_MIPStarRE_LDT_avgOver_sum
import Theorems.Thm_MIPStarRE_LDT_avgOver_zero
import Theorems.Thm_MIPStarRE_LDT_ev_finset_sum
import Theorems.Thm_MIPStarRE_LDT_ev_leftTensor_total_eq_sum_outcome
import Theorems.Thm_MIPStarRE_LDT_leftTensor_finset_sum
import Theorems.Thm_MIPStarRE_LDT_leftTensor_nonneg

attribute [simp] MIPStarRE.LDT.Polynomial.restrictToAxisParallelLine_apply

set_option backward.isDefEq.respectTransparency false

/-!
# Section 12 pasting: over all outcomes — Schwartz–Zippel bounds and final assembly

Schwartz–Zippel aggregation, the line-consistent indicator bound, and the final chained
assembly of `lem:over-all-outcomes`.

## References

- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- For a fixed distinct tuple and interpolation-eligible nonglobal outcome, the
probability (over the vertical-line base point `u`) of the line-consistency
indicator is bounded by the paper's `md/q` Schwartz--Zippel term.

This formalizes `ld-pasting.tex` lines 1256--1265: nonglobality gives a supported
slice where `gᵢ` differs from the interpolant `h*`; line consistency forces
agreement at the sampled `u`, and `Preliminaries.polynomialAgreement_avg_le_mdq`
bounds that agreement probability. -/
lemma lineConsistentIndicator_probability_le_mdq
    (params : Parameters) [FieldModel params.q]
    {k : ℕ}
    (xs : PointTuple params k)
    (hxs : Function.Injective xs)
    (gs : GHatTupleOutcome params k)
    (hEligible : InterpolationEligible params gs) :
    avgOver (uniformDistribution (Point params)) (fun u =>
        if (¬ IsGloballyConsistent params xs gs) ∧
            ∃ f : AxisLinePolynomial params.next,
              ¬ (∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
                ((gs i).get hiSome) u ≠ f (xs i)) then
          (1 : Error)
        else 0) ≤
      ((params.m * params.d : ℕ) : Error) / (params.q : Error) := by
  classical
  let δ : Error := ((params.m * params.d : ℕ) : Error) / (params.q : Error)
  have hδ_nonneg : 0 ≤ δ := by
    dsimp [δ]
    positivity
  by_cases hGlobal : IsGloballyConsistent params xs gs
  · calc
      avgOver (uniformDistribution (Point params)) (fun u =>
          if (¬ IsGloballyConsistent params xs gs) ∧
              ∃ f : AxisLinePolynomial params.next,
                ¬ (∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
                  ((gs i).get hiSome) u ≠ f (xs i)) then
            (1 : Error)
          else 0) = 0 := by
            simp [hGlobal, avgOver_zero]
      _ ≤ ((params.m * params.d : ℕ) : Error) / (params.q : Error) := hδ_nonneg
  · rcases nonglobal_gives_slice_mismatch_against_interpolant params xs gs hGlobal with
      ⟨i, hiSome, hsliceNe⟩
    let hStarSlice : Polynomial params :=
      Polynomial.restrictAtHeight params (interpolateCompletedSlices params k xs gs) (xs i)
    have hneq : (gs i).get hiSome ≠ hStarSlice := by
      intro hEq
      exact hsliceNe (by simpa [hStarSlice] using hEq.symm)
    have hpoint : ∀ u : Point params,
        (if (¬ IsGloballyConsistent params xs gs) ∧
            ∃ f : AxisLinePolynomial params.next,
              ¬ (∃ j : Fin k, ∃ hjSome : (gs j).isSome = true,
                ((gs j).get hjSome) u ≠ f (xs j)) then
          (1 : Error)
        else 0) ≤
          if ((gs i).get hiSome) u = hStarSlice u then (1 : Error) else 0 := by
      intro u
      by_cases hCons : (¬ IsGloballyConsistent params xs gs) ∧
          ∃ f : AxisLinePolynomial params.next,
            ¬ (∃ j : Fin k, ∃ hjSome : (gs j).isSome = true,
              ((gs j).get hjSome) u ≠ f (xs j))
      · rcases hCons.2 with ⟨f, hNoMismatch⟩
        have hLine := tupleInterpolatedVerticalLine_eq_of_no_supported_mismatch
          params u xs hxs gs hEligible f hNoMismatch
        have htupleEval :
            tupleInterpolatedVerticalLine params u xs gs (xs i) = hStarSlice u := by
          dsimp [hStarSlice]
          simpa [tupleInterpolatedVerticalLine] using
            restrictToVerticalLine_eval_eq_restrictAtHeight_eval
              params (interpolateCompletedSlices params k xs gs) u (xs i)
        have hsliceEq : ((gs i).get hiSome) u = hStarSlice u := by
          have hnotNe : ¬ ((gs i).get hiSome) u ≠ f (xs i) := by
            intro hne
            exact hNoMismatch ⟨i, hiSome, hne⟩
          have hgf : ((gs i).get hiSome) u = f (xs i) := by
            by_contra hne
            exact hnotNe hne
          exact hgf.trans
            ((congrArg (fun line : AxisLinePolynomial params.next => line (xs i))
              hLine.symm).trans htupleEval)
        rw [if_pos hCons, if_pos hsliceEq]
      · rw [if_neg hCons]
        by_cases hEq : ((gs i).get hiSome) u = hStarSlice u <;> simp [hEq]
    calc
      avgOver (uniformDistribution (Point params)) (fun u =>
          if (¬ IsGloballyConsistent params xs gs) ∧
              ∃ f : AxisLinePolynomial params.next,
                ¬ (∃ j : Fin k, ∃ hjSome : (gs j).isSome = true,
                  ((gs j).get hjSome) u ≠ f (xs j)) then
            (1 : Error)
          else 0)
        ≤ avgOver (uniformDistribution (Point params)) (fun u =>
            if ((gs i).get hiSome) u = hStarSlice u then (1 : Error) else 0) := by
            exact avgOver_mono _ _ _ hpoint
      _ ≤ δ := by
            simpa [δ, hStarSlice] using
              Preliminaries.polynomialAgreement_avg_le_mdq
                params ((gs i).get hiSome) hStarSlice hneq

/-- Expand an averaged restricted lifted submeasurement into per-outcome masses
weighted by the probability of the restricting predicate. -/
lemma avgOver_subMeasMass_restrict_liftLeft_eq_sum_coeff
    {Question Outcome : Type*} [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (𝒟 : Distribution Question)
    (A : SubMeas Outcome ι)
    (P : Question → Outcome → Prop) [∀ q, DecidablePred (P q)] :
    avgOver 𝒟 (fun q => subMeasMass ψ ((restrictSubMeas A (P q)).liftLeft)) =
      ∑ a : Outcome,
        avgOver 𝒟 (fun q => if P q a then (1 : Error) else 0) *
          ev ψ (leftTensor (ι₂ := ι) (A.outcome a)) := by
  classical
  calc
    avgOver 𝒟 (fun q => subMeasMass ψ ((restrictSubMeas A (P q)).liftLeft))
      = avgOver 𝒟 (fun q =>
          ∑ a : Outcome,
            if P q a then ev ψ (leftTensor (ι₂ := ι) (A.outcome a)) else 0) := by
          apply avgOver_congr
          intro q
          unfold subMeasMass SubMeas.liftLeft restrictSubMeas
          rw [mkLeftPlacedSubMeas_total]
          rw [← leftTensor_finset_sum (ι₂ := ι)
            (Finset.univ.filter (P q)) (fun a => A.outcome a)]
          rw [ev_finset_sum]
          rw [Finset.sum_filter]
    _ = ∑ a : Outcome,
        avgOver 𝒟 (fun q =>
          if P q a then ev ψ (leftTensor (ι₂ := ι) (A.outcome a)) else 0) :=
          avgOver_sum 𝒟 (fun q a =>
            if P q a then ev ψ (leftTensor (ι₂ := ι) (A.outcome a)) else 0)
    _ = ∑ a : Outcome,
        avgOver 𝒟 (fun q => (if P q a then (1 : Error) else 0) *
          ev ψ (leftTensor (ι₂ := ι) (A.outcome a))) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          apply avgOver_congr
          intro q
          by_cases hp : P q a <;> simp [hp]
    _ = ∑ a : Outcome,
        avgOver 𝒟 (fun q => if P q a then (1 : Error) else 0) *
          ev ψ (leftTensor (ι₂ := ι) (A.outcome a)) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [avgOver_mul_const]

/-- Fixed-distinct-tuple form of the line-consistent Schwartz--Zippel bound. -/
lemma lineConsistentIndicatorLocal_avg_le_mdq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) {k : ℕ}
    (xs : PointTuple params k)
    (hxs : Function.Injective xs) :
    avgOver (uniformDistribution (Point params)) (fun u =>
        overAllOutcomesLineConsistentIndicatorLocal params strategy family u xs) ≤
      ((params.m * params.d : ℕ) : Error) / (params.q : Error) := by
  classical
  let δ : Error := ((params.m * params.d : ℕ) : Error) / (params.q : Error)
  let A := interpolationEligibleSandwichFamily params family k xs
  let P : Point params → GHatTupleOutcome params k → Prop := fun u gs =>
    (¬ IsGloballyConsistent params xs gs) ∧
      ∃ f : AxisLinePolynomial params.next,
        ¬ (∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
          ((gs i).get hiSome) u ≠ f (xs i))
  have hδ_nonneg : 0 ≤ δ := by
    dsimp [δ]
    positivity
  have hmass_nonneg : ∀ gs : GHatTupleOutcome params k,
      0 ≤ ev strategy.state (leftTensor (ι₂ := ι) (A.outcome gs)) := by
    intro gs
    exact ev_nonneg_of_psd strategy.state _ <|
      leftTensor_nonneg (ι₂ := ι) (A.outcome_pos gs)
  calc
    avgOver (uniformDistribution (Point params)) (fun u =>
        overAllOutcomesLineConsistentIndicatorLocal params strategy family u xs)
      = ∑ gs : GHatTupleOutcome params k,
          avgOver (uniformDistribution (Point params))
            (fun u => if P u gs then (1 : Error) else 0) *
            ev strategy.state (leftTensor (ι₂ := ι) (A.outcome gs)) := by
          unfold overAllOutcomesLineConsistentIndicatorLocal
          dsimp [A, P]
          exact avgOver_subMeasMass_restrict_liftLeft_eq_sum_coeff
            strategy.state (uniformDistribution (Point params)) A P
    _ ≤ ∑ gs : GHatTupleOutcome params k,
          δ * ev strategy.state (leftTensor (ι₂ := ι) (A.outcome gs)) := by
          refine Finset.sum_le_sum ?_
          intro gs _
          by_cases hEligible : InterpolationEligible params gs
          · have hprob := lineConsistentIndicator_probability_le_mdq
              params xs hxs gs hEligible
            exact mul_le_mul_of_nonneg_right (by simpa [P, δ] using hprob)
              (hmass_nonneg gs)
          · have hAout : A.outcome gs = 0 := by
              simp [A, interpolationEligibleSandwichFamily, restrictSubMeas, hEligible]
            simp [hAout, leftTensor, ev]
    _ = δ * ∑ gs : GHatTupleOutcome params k,
          ev strategy.state (leftTensor (ι₂ := ι) (A.outcome gs)) := by
          rw [Finset.mul_sum]
    _ = δ * subMeasMass strategy.state A.liftLeft := by
          change δ * ∑ gs : GHatTupleOutcome params k,
              ev strategy.state (leftTensor (ι₂ := ι) (A.outcome gs)) =
            δ * ev strategy.state (leftTensor (ι₂ := ι) A.total)
          rw [ev_leftTensor_total_eq_sum_outcome strategy.state A]
    _ ≤ δ * 1 := by
          exact mul_le_mul_of_nonneg_left
            (eligibleMass_le_one params strategy family xs) hδ_nonneg
    _ = ((params.m * params.d : ℕ) : Error) / (params.q : Error) := by
          simp [δ]

/-- The line-consistent Schwartz--Zippel aggregation after the insertion and
bad-line finite-sum split.

Paper anchor: `ld-pasting.tex` lines 1235--1275.  For every distinct tuple `xs`,
interpolation-eligible nonglobal outcome `gs`, and line-consistent answer `f`, the
paper chooses the interpolant `h*`; nonglobality gives a supported coordinate
where `gᵢ ≠ h*|_{xsᵢ}`, and Schwartz--Zippel bounds the probability over `u` that
this disagreement vanishes by `md/q`. -/
lemma overAllOutcomes_distinct_lineConsistent_indicator_mass_le_mdq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ) :
    overAllOutcomesDistinctLineConsistentIndicatorMass params strategy family k ≤
      ((params.m * params.d : ℕ) : Error) / (params.q : Error) := by
  classical
  let δ : Error := ((params.m * params.d : ℕ) : Error) / (params.q : Error)
  have hδ_nonneg : 0 ≤ δ := by
    dsimp [δ]
    positivity
  unfold overAllOutcomesDistinctLineConsistentIndicatorMass
  rw [avgOver_comm (uniformDistribution (Point params))
    (distinctTupleDistribution params k)
    (fun u xs => overAllOutcomesLineConsistentIndicatorLocal params strategy family u xs)]
  calc
    avgOver (distinctTupleDistribution params k) (fun xs =>
        avgOver (uniformDistribution (Point params)) (fun u =>
          overAllOutcomesLineConsistentIndicatorLocal params strategy family u xs))
      ≤ avgOver (distinctTupleDistribution params k) (fun _ => δ) := by
          refine avgOver_mono_on_support (distinctTupleDistribution params k) _ _ ?_
          intro xs hxs_mem
          have hxs : Function.Injective xs := by
            simpa [distinctTupleDistribution] using hxs_mem
          simpa [δ] using
            lineConsistentIndicatorLocal_avg_le_mdq params strategy family xs hxs
    _ ≤ δ := by
          unfold avgOver
          calc
            ∑ xs ∈ (distinctTupleDistribution params k).support,
                (distinctTupleDistribution params k).weight xs * δ
              = (∑ xs ∈ (distinctTupleDistribution params k).support,
                  (distinctTupleDistribution params k).weight xs) * δ := by
                  rw [← Finset.sum_mul]
            _ ≤ 1 * δ := by
                  exact mul_le_mul_of_nonneg_right
                    (distinctTupleDistribution_weight_sum_le_one params k) hδ_nonneg
            _ = δ := by ring
    _ = ((params.m * params.d : ℕ) : Error) / (params.q : Error) := by
          try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal

/-- The local finite-sum/SZ comparison after the one-point line-mismatch
aggregation has been separated off.

The insertion and finite-sum split from `ld-pasting.tex` lines 1174--1228 are
proved by `overAllOutcomes_distinct_nonglobal_mass_le_bad_line_mass_add_lineConsistent`.
The line-consistent remainder is exactly the Schwartz--Zippel aggregation proved
by `overAllOutcomes_distinct_lineConsistent_indicator_mass_le_mdq`, corresponding
to lines 1235--1275. -/
lemma overAllOutcomes_distinct_nonglobal_mass_le_bad_line_mass_add_mdq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ) :
    overAllOutcomesDistinctNonglobalMass params strategy family k ≤
      overAllOutcomesDistinctBadLineMass params strategy family k +
        ((params.m * params.d : ℕ) : Error) / (params.q : Error) := by
  have hsplit :=
    overAllOutcomes_distinct_nonglobal_mass_le_bad_line_mass_add_lineConsistent
      params strategy family k
  have hindicator := lineConsistentNonglobalMass_le_indicatorMass
    params strategy family k
  have hsz :=
    overAllOutcomes_distinct_lineConsistent_indicator_mass_le_mdq
      params strategy family k
  linarith

/-- If the distinct nonglobal mass is bounded by the paper's local
`k·ν₅ + k²/q + md/q` comparison, then the reverse half of
`lem:over-all-outcomes` follows.

The remaining hypothesis is exactly the content of `ld-pasting.tex` lines
1174--1275: insert the line measurement, pay the one-point line consistency
bound to add the consistency indicator, and use Schwartz--Zippel for the
indicator term. -/
lemma overAllOutcomes_reverse_mass_bound_of_nonglobal_mass_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma zeta : Error) (k : ℕ)
    (hd : 0 < params.d)
    (hdq_le : params.d ≤ params.q)
    (hkEligible : params.d + 1 ≤ k)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta)
    (hnonglobal :
      overAllOutcomesDistinctNonglobalMass params strategy family k ≤
        hBConsistencyError params eps delta gamma zeta k +
          ((params.m * params.d : ℕ) : Error) / (params.q : Error)) :
    overAllOutcomesExpansionMass params strategy family k -
        overAllOutcomesPastedMass params strategy family k ≤
      overAllOutcomesError params eps delta gamma zeta k := by
  have hswap := avgOver_uniform_eligibleMass_le_distinct_add_dnoteq
    params strategy family k
  have hsplit := avgOver_distinct_eligibleMass_eq_global_add_nonglobal
    params strategy family k
  rw [overAllOutcomesExpansionMass_eq_avg_uniform_eligible,
    overAllOutcomesPastedMass_eq_avg_distinct_global]
  have hbound := hBConsistencyError_add_mdq_add_dnoteq_le_overAllOutcomesError
    params eps delta gamma zeta k hd hdq_le hkEligible
    heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg
  linarith

/-- The paper-local nonglobal mass comparison after the algebraic reductions.

The one-point line-comparison aggregation from `ld-pasting.tex` lines 1186--1202
is proved by `overAllOutcomes_distinct_bad_line_mass_le_hBConsistencyError`, and
the remaining insertion/Schwartz--Zippel estimate is
`overAllOutcomes_distinct_nonglobal_mass_le_bad_line_mass_add_mdq`. -/
lemma overAllOutcomes_distinct_nonglobal_mass_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma zeta : Error) (k : ℕ)
    (hd : 0 < params.d)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta)
    (hline : ∀ i : ℕ, i < k →
      LdSandwichLineOnePointStatement params strategy family
        eps delta gamma zeta k i) :
    overAllOutcomesDistinctNonglobalMass params strategy family k ≤
      hBConsistencyError params eps delta gamma zeta k +
        ((params.m * params.d : ℕ) : Error) / (params.q : Error) := by
  have hlocal :=
    overAllOutcomes_distinct_nonglobal_mass_le_bad_line_mass_add_mdq
      params strategy family k
  have hbad :=
    overAllOutcomes_distinct_bad_line_mass_le_hBConsistencyError
      params strategy family eps delta gamma zeta k hd
      heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg hline
  linarith

/-- Reduction of `lem:over-all-outcomes` to a reverse mass comparison.

The forward direction
`overAllOutcomesPastedMass - overAllOutcomesExpansionMass` is now discharged by
expanding the pasted mass over distinct tuples, forgetting global consistency,
and paying only `ldDnoteq`.  The reverse loss
`overAllOutcomesExpansionMass - overAllOutcomesPastedMass` is the part of
`ld-pasting.tex` supplied below by the completed `ldSandwichLineOnePoint`
aggregation. -/
lemma overAllOutcomes_of_reverse_mass_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma zeta : Error) (k : ℕ)
    (hd : 0 < params.d)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta)
    (hreverse :
      overAllOutcomesExpansionMass params strategy family k -
          overAllOutcomesPastedMass params strategy family k ≤
        overAllOutcomesError params eps delta gamma zeta k) :
    OverAllOutcomesStatement params strategy family eps delta gamma zeta k := by
  refine ⟨?_⟩
  have hforward_dnoteq := overAllOutcomes_pasted_sub_expansion_le_dnoteq
    params strategy family k
  have hforward :
      overAllOutcomesPastedMass params strategy family k -
          overAllOutcomesExpansionMass params strategy family k ≤
        overAllOutcomesError params eps delta gamma zeta k := by
    exact le_trans hforward_dnoteq
      (dnoteq_term_le_overAllOutcomesError params eps delta gamma zeta k hd
        heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg)
  exact abs_le.mpr ⟨by linarith, hforward⟩

end MIPStarRE.LDT.Pasting


