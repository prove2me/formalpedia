-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Main_Auxiliary_ScalarMarginalization
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Main_Auxiliary_ScalarMarginalization
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T04:07:10.145743+00:00
-- url     : https://prove2.me/theorems/1d7426d6-7620-44c7-a304-21f97fecf790
-- title:
--   Definitions of ScalarMarginalization: Section 11 commutativity: scalar marginalization lemmas Schwartz–Zippel marginalization helpers…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Commutativity.Main.Auxiliary.ScalarMarginalization` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Section 11 commutativity: scalar marginalization lemmas. Schwartz–Zippel marginalization helpers (`eq:evaluate-gcom-at-points`, `eq:gcom4-diff`) used in the final full-slice commutation theorem. The public lemmas `fullSlice_scalar_marginalize_x` and `fullSlice_scalar_marginalize_y` are pure scalar inequalities. Their proofs compose internal tensor-form comparisons over the tensor averages defined in `Transport/FullSlice/Averages.lean`, with `closenessOfIP` at cost `√ζ` each. See `docs/decisions/713-scalar-tensor-decision.md` for the full decision record.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Definitions** (1): `_private.MIPRE.Background.LIDT.MIPStarRE.LDT.Commutativity.Main.Auxiliary.ScalarMarginalization.0.MIPStarRE.LDT.Commutativity.evaluatedPointProj` (The evaluated point family viewed as a projective submeasurement family.).
--
--   **Embedded lemmas** (7): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `abs_sub_le_of_two_step`, `avgOver_slice_total_left_sandwich_eq`, `evaluatedSliceABAAvg_eq_leftSandwichExpectation`, `fullSliceABAAvg_eq_leftSandwichExpectation`, `fullSlice_middleSandwichExpectation_eq_evaluated`, `sum_ev_leftTensor_sandwich_total`, `sum_ev_middle_total`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Commutativity.Main.Auxiliary.ScalarMarginalization` (`MIPRE/Background/LIDT/MIPStarRE/LDT/Commutativity/Main/Auxiliary/ScalarMarginalization.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 58 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/Commutativity/Main/Auxiliary/ScalarMarginalization.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Commutativity/Main/Auxiliary/ScalarMarginalization.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Commutativity/Main/Auxiliary/ScalarMarginalization.lean (definition bundle: declarations the uploaded statements rest on);
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
import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Notation.Defs
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
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.CStarAlgebra.Module.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Order
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
import Mathlib.Data.Set.Defs
import Mathlib.Data.SetLike.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Logic.Basic
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
import Theorems.Thm_MIPStarRE_LDT_CommutativityPoints_avgOver_uniform_pointNext_height
import Theorems.Thm_MIPStarRE_LDT_averageOperatorOverDistribution_mul_left_right
import Theorems.Thm_MIPStarRE_LDT_avgOver_congr
import Theorems.Thm_MIPStarRE_LDT_avgOver_sum
import Theorems.Thm_MIPStarRE_LDT_avgOver_uniform_prod
import Theorems.Thm_MIPStarRE_LDT_ev_leftTensor_averageOperatorOverDistribution
import Theorems.Thm_MIPStarRE_LDT_ev_sum
import Theorems.Thm_MIPStarRE_LDT_leftTensor_finset_sum
import Theorems.Thm_MIPStarRE_LDT_leftTensor_mul_leftTensor
import Theorems.Thm_MIPStarRE_LDT_postprocess_total
import Theorems.Thm_MIPStarRE_LDT_rightTensor_finset_sum

set_option backward.isDefEq.respectTransparency false

/-!
# Section 11 commutativity: scalar marginalization lemmas

Schwartz–Zippel marginalization helpers (`eq:evaluate-gcom-at-points`,
`eq:gcom4-diff`) used in the final full-slice commutation theorem.

The public lemmas `fullSlice_scalar_marginalize_x` and
`fullSlice_scalar_marginalize_y` are pure scalar inequalities.  Their proofs
compose internal tensor-form comparisons over the tensor averages defined in
`Transport/FullSlice/Averages.lean`, with `closenessOfIP` at cost `√ζ` each.

See `docs/decisions/713-scalar-tensor-decision.md` for the full decision record.

## References

- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The evaluated point family viewed as a projective submeasurement family. -/
noncomputable def evaluatedPointProj
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxProjSubMeas (Point params.next) (Fq params) ι :=
  fun u =>
    { toSubMeas := evaluatedPointFamily params family u
      proj := evaluatedPointFamily_outcome_proj params family u }

/-- Triangle inequality with explicit bounds for an intermediate point. -/
lemma abs_sub_le_of_two_step
    {a b c e₁ e₂ : Error}
    (hab : |a - b| ≤ e₁) (hbc : |b - c| ≤ e₂) :
    |a - c| ≤ e₁ + e₂ :=
  (abs_sub_le a b c).trans (add_le_add hab hbc)

/-- Summing the inner outcome in an `ABA` expectation turns it into the
submeasurement total. -/
lemma sum_ev_leftTensor_sandwich_total
    {α : Type*} [Fintype α]
    (ψ : QuantumState (ι × ι)) (A : MIPStarRE.Quantum.Op ι) (B : SubMeas α ι) :
    (∑ b : α, ev ψ (leftTensor (ι₂ := ι) (A * B.outcome b * A))) =
      ev ψ (leftTensor (ι₂ := ι) (A * B.total * A)) := by
  rw [← ev_sum ψ (fun b : α => leftTensor (ι₂ := ι) (A * B.outcome b * A))]
  congr 1
  rw [← B.sum_eq_total]
  rw [Matrix.mul_sum]
  rw [Matrix.sum_mul]
  rw [leftTensor_finset_sum]

/-- Summing the right-register outcome in the middle switch-sandwich term turns
it into the submeasurement total. -/
lemma sum_ev_middle_total
    {α : Type*} [Fintype α]
    (ψ : QuantumState (ι × ι)) (G : MIPStarRE.Quantum.Op ι) (A : SubMeas α ι) :
    (∑ a : α, ev ψ (leftTensor (ι₂ := ι) G * rightTensor (ι₁ := ι) (A.outcome a))) =
      ev ψ (leftTensor (ι₂ := ι) G * rightTensor (ι₁ := ι) A.total) := by
  rw [← ev_sum ψ (fun a : α => leftTensor (ι₂ := ι) G *
    rightTensor (ι₁ := ι) (A.outcome a))]
  congr 1
  rw [← A.sum_eq_total]
  rw [← Matrix.mul_sum]
  rw [rightTensor_finset_sum]

/-- Averaging the middle total in an `ABA` sandwich produces the averaged
slice operator `G = E_y Gʸ`. -/
lemma avgOver_slice_total_left_sandwich_eq
    (params : Parameters) [FieldModel params.q]
    (ψ : QuantumState (ι × ι)) (family : IdxPolyFamily params ι)
    (A : MIPStarRE.Quantum.Op ι) :
    avgOver (uniformDistribution (Fq params))
        (fun y => ev ψ (leftTensor (ι₂ := ι) (A * (family.meas y).total * A))) =
      ev ψ (leftTensor (ι₂ := ι) A *
        leftTensor (ι₂ := ι) (IdxPolyFamily.averagedSubMeas family).total *
        leftTensor (ι₂ := ι) A) := by
  rw [← ev_leftTensor_averageOperatorOverDistribution ψ (uniformDistribution (Fq params))
    (fun y => A * (family.meas y).total * A)]
  rw [averageOperatorOverDistribution_mul_left_right]
  simp [IdxPolyFamily.averagedSubMeas, averageIdxSubMeas,
    leftTensor_mul_leftTensor, mul_assoc]

/-- Full-slice cubic first term as the left switch-sandwich expectation. -/
lemma fullSliceABAAvg_eq_leftSandwichExpectation
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    fullSliceABAAvg params strategy family =
      MIPStarRE.LDT.Preliminaries.leftSandwichExpectation strategy.state
        (uniformDistribution (Fq params)) family.meas
        ((IdxPolyFamily.averagedSubMeas family).total) := by
  classical
  unfold fullSliceABAAvg MIPStarRE.LDT.Preliminaries.leftSandwichExpectation
  rw [avgOver_uniform_prod (α := Fq params) (β := Fq params) (f := fun x y =>
    ∑ gh : FullSliceOutcome params,
      ev strategy.state (leftTensor (ι₂ := ι)
        ((family.meas x).toSubMeas.outcome gh.1 *
          (family.meas y).toSubMeas.outcome gh.2 *
          (family.meas x).toSubMeas.outcome gh.1)))]
  apply avgOver_congr
  intro x
  simp only [Fintype.sum_prod_type]
  rw [avgOver_sum]
  apply Finset.sum_congr rfl
  intro g _
  calc
    avgOver (uniformDistribution (Fq params))
        (fun y => ∑ h : Polynomial params,
          ev strategy.state (leftTensor (ι₂ := ι)
            ((family.meas x).outcome g * (family.meas y).outcome h *
              (family.meas x).outcome g)))
        = avgOver (uniformDistribution (Fq params))
            (fun y => ev strategy.state (leftTensor (ι₂ := ι)
              ((family.meas x).outcome g * (family.meas y).total *
                (family.meas x).outcome g))) := by
            apply avgOver_congr
            intro y
            exact sum_ev_leftTensor_sandwich_total strategy.state
              ((family.meas x).outcome g) (family.meas y).toSubMeas
    _ = ev strategy.state
          (leftTensor (ι₂ := ι) ((family.meas x).outcome g) *
            leftTensor (ι₂ := ι) (IdxPolyFamily.averagedSubMeas family).total *
            leftTensor (ι₂ := ι) ((family.meas x).outcome g)) := by
            exact avgOver_slice_total_left_sandwich_eq params strategy.state family
              ((family.meas x).outcome g)

/-- Evaluated-slice cubic first term as the evaluated left switch-sandwich expectation. -/
lemma evaluatedSliceABAAvg_eq_leftSandwichExpectation
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    evaluatedSliceABAAvg params strategy family =
      MIPStarRE.LDT.Preliminaries.leftSandwichExpectation strategy.state
        (uniformDistribution (Point params.next))
        (evaluatedPointProj params family)
        ((IdxPolyFamily.averagedSubMeas family).total) := by
  classical
  unfold evaluatedSliceABAAvg MIPStarRE.LDT.Preliminaries.leftSandwichExpectation
    evaluatedPointProj
  change avgOver (uniformDistribution (Point params.next × Point params.next))
      (fun uv => (fun u v => ∑ ab : Fq params × Fq params,
        evaluatedSliceABATerm params strategy family (u, v) ab) uv.1 uv.2) =
    avgOver (uniformDistribution (Point params.next))
      (fun q => ∑ a : Fq params,
        ev strategy.state
          (leftTensor (ι₂ := ι) ((evaluatedPointFamily params family q).outcome a) *
            leftTensor (ι₂ := ι) (IdxPolyFamily.averagedSubMeas family).total *
            leftTensor (ι₂ := ι) ((evaluatedPointFamily params family q).outcome a)))
  rw [avgOver_uniform_prod (α := Point params.next) (β := Point params.next)
    (f := fun u v => ∑ ab : Fq params × Fq params,
      evaluatedSliceABATerm params strategy family (u, v) ab)]
  apply avgOver_congr
  intro u
  simp only [Fintype.sum_prod_type]
  rw [avgOver_sum]
  apply Finset.sum_congr rfl
  intro a _
  unfold evaluatedSliceABATerm
  calc
    avgOver (uniformDistribution (Point params.next))
        (fun v => ∑ b : Fq params,
          ev strategy.state (leftTensor (ι₂ := ι)
            ((evaluatedPointFamily params family u).outcome a *
              (evaluatedPointFamily params family v).outcome b *
              (evaluatedPointFamily params family u).outcome a)))
        = avgOver (uniformDistribution (Point params.next))
            (fun v => ev strategy.state (leftTensor (ι₂ := ι)
              ((evaluatedPointFamily params family u).outcome a *
                (evaluatedPointFamily params family v).total *
                (evaluatedPointFamily params family u).outcome a))) := by
            apply avgOver_congr
            intro v
            exact sum_ev_leftTensor_sandwich_total strategy.state
              ((evaluatedPointFamily params family u).outcome a)
              (evaluatedPointFamily params family v)
    _ = avgOver (uniformDistribution (Fq params))
          (fun y => ev strategy.state (leftTensor (ι₂ := ι)
            ((evaluatedPointFamily params family u).outcome a *
              (family.meas y).total *
              (evaluatedPointFamily params family u).outcome a))) := by
            have h := CommutativityPoints.avgOver_uniform_pointNext_height params
              (fun y : Fq params => ev strategy.state (leftTensor (ι₂ := ι)
                ((evaluatedPointFamily params family u).outcome a *
                  (family.meas y).total *
                  (evaluatedPointFamily params family u).outcome a)))
            rw [← h]
            apply avgOver_congr
            intro v
            simp [evaluatedPointFamily, IdxPolyFamily.evaluatedAtNextPoint, evaluateAt,
              postprocess_total]
    _ = ev strategy.state
          (leftTensor (ι₂ := ι) ((evaluatedPointFamily params family u).outcome a) *
            leftTensor (ι₂ := ι) (IdxPolyFamily.averagedSubMeas family).total *
            leftTensor (ι₂ := ι) ((evaluatedPointFamily params family u).outcome a)) := by
            exact avgOver_slice_total_left_sandwich_eq params strategy.state family
              ((evaluatedPointFamily params family u).outcome a)

/-- The full and evaluated switch-sandwich middle terms are the same `G ⊗ G` average. -/
lemma fullSlice_middleSandwichExpectation_eq_evaluated
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    MIPStarRE.LDT.Preliminaries.middleSandwichExpectation strategy.state
        (uniformDistribution (Fq params)) family.meas
        ((IdxPolyFamily.averagedSubMeas family).total) =
      MIPStarRE.LDT.Preliminaries.middleSandwichExpectation strategy.state
        (uniformDistribution (Point params.next))
        (evaluatedPointProj params family)
        ((IdxPolyFamily.averagedSubMeas family).total) := by
  classical
  unfold MIPStarRE.LDT.Preliminaries.middleSandwichExpectation evaluatedPointProj
  let G : MIPStarRE.Quantum.Op ι := (IdxPolyFamily.averagedSubMeas family).total
  change avgOver (uniformDistribution (Fq params))
      (fun x => ∑ a : Polynomial params,
        ev strategy.state (leftTensor (ι₂ := ι) G *
          rightTensor (ι₁ := ι) ((family.meas x).outcome a))) =
    avgOver (uniformDistribution (Point params.next))
      (fun u => ∑ a : Fq params,
        ev strategy.state (leftTensor (ι₂ := ι) G *
          rightTensor (ι₁ := ι) ((evaluatedPointFamily params family u).outcome a)))
  calc
    avgOver (uniformDistribution (Fq params))
        (fun x => ∑ a : Polynomial params,
          ev strategy.state (leftTensor (ι₂ := ι) G *
            rightTensor (ι₁ := ι) ((family.meas x).outcome a))) =
      avgOver (uniformDistribution (Fq params))
        (fun x => ev strategy.state (leftTensor (ι₂ := ι) G *
          rightTensor (ι₁ := ι) ((family.meas x).total))) := by
        apply avgOver_congr
        intro x
        exact sum_ev_middle_total strategy.state G (family.meas x).toSubMeas
    _ = avgOver (uniformDistribution (Point params.next))
        (fun u => ev strategy.state (leftTensor (ι₂ := ι) G *
          rightTensor (ι₁ := ι) ((evaluatedPointFamily params family u).total))) := by
        symm
        calc
          avgOver (uniformDistribution (Point params.next))
              (fun u => ev strategy.state (leftTensor (ι₂ := ι) G *
                rightTensor (ι₁ := ι) ((evaluatedPointFamily params family u).total))) =
            avgOver (uniformDistribution (Point params.next))
              (fun u => ev strategy.state (leftTensor (ι₂ := ι) G *
                rightTensor (ι₁ := ι) ((family.meas (pointHeight params u)).total))) := by
              apply avgOver_congr
              intro u
              simp [evaluatedPointFamily, IdxPolyFamily.evaluatedAtNextPoint, evaluateAt,
                postprocess_total]
          _ = avgOver (uniformDistribution (Fq params))
              (fun x => ev strategy.state (leftTensor (ι₂ := ι) G *
                rightTensor (ι₁ := ι) ((family.meas x).total))) := by
              exact CommutativityPoints.avgOver_uniform_pointNext_height params
                (fun x : Fq params => ev strategy.state (leftTensor (ι₂ := ι) G *
                  rightTensor (ι₁ := ι) ((family.meas x).total)))
    _ = avgOver (uniformDistribution (Point params.next))
        (fun u => ∑ a : Fq params,
          ev strategy.state (leftTensor (ι₂ := ι) G *
            rightTensor (ι₁ := ι) ((evaluatedPointFamily params family u).outcome a))) := by
        apply avgOver_congr
        intro u
        exact (sum_ev_middle_total strategy.state G (evaluatedPointFamily params family u)).symm

end MIPStarRE.LDT.Commutativity


