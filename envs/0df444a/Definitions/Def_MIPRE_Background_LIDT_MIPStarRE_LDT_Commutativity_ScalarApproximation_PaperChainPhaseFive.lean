-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_PaperChainPhaseFive
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_PaperChainPhaseFive
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T03:48:54.336502+00:00
-- url     : https://prove2.me/theorems/aaebe267-8bb1-46ad-a962-776df586535e
-- title:
--   Definitions of PaperChainPhaseFive: Phase-five endpoint for the evaluated-slice paper chain This file isolates the paper line-87 removal endpoint and the…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Commutativity.ScalarApproximation.PaperChainPhaseFive` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Phase-five endpoint for the evaluated-slice paper chain. This file isolates the paper line-87 removal endpoint and the finite reindexing to the raw scalar `G`-commutativity stability defect.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Definitions** (7): `MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseEightTailRight` (Paper line 118 endpoint after moving the second factor to the right register.); `MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseFivePaperOrderedDefect` (Ordered missing-mass defect for the paper phase-five removal.); `MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseFivePaperRemoved` (Paper line-87 endpoint after removing the trailing `G^x.total`.); `MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseFivePaperSwappedDefect` (Swapped missing-mass defect for the paper phase-five removal.); `MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseSevenGonnaCite` (Paper line 104 endpoint `eq:gonna-cite-this-in-just-a-bit`.); `MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseSixFirstRemoved` (Paper line 102 endpoint after simplifying the first-coordinate projector.); `MIPStarRE.LDT.Commutativity.evaluatedSlicePhaseSixFirstReverse` (Paper line 101 endpoint after reversing the first `eq:add-an-a` insertion.).
--
--   **Embedded lemmas** (3): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `evaluatedSlicePhaseFivePaperSwappedDefect_appendPoint_expansion`, `evaluatedSlice_phaseFivePaper_term_diff`, `phaseFivePaper_fiber_sum_ev`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Commutativity.ScalarApproximation.PaperChainPhaseFive` (`MIPRE/Background/LIDT/MIPStarRE/LDT/Commutativity/ScalarApproximation/PaperChainPhaseFive.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 49 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/Commutativity/ScalarApproximation/PaperChainPhaseFive.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Commutativity/ScalarApproximation/PaperChainPhaseFive.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Commutativity/ScalarApproximation/PaperChainPhaseFive.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.NonUnitalHom
import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
import Mathlib.Algebra.BigOperators.Field
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
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Algebra.MvPolynomial.Rename
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
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.List.Nodup
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Multiset.Defs
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Prod.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
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
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_CommutativityPoints_SharedHelpers_SharedLine
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_CommutativityPoints_BridgeTheorems_DropBridges
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_GCommStability_Scalar_RawSecond
import Theorems.Thm_MIPStarRE_LDT_Commutativity_ev_leftTensor_mul_middle_finset_sum
import Theorems.Thm_MIPStarRE_LDT_Commutativity_evaluatedPointFamily_appendPoint_outcome
import Theorems.Thm_MIPStarRE_LDT_Commutativity_evaluatedPointFamily_total_eq_G_total
import Theorems.Thm_MIPStarRE_LDT_ev_scale
import Theorems.Thm_MIPStarRE_LDT_ev_sub
import Theorems.Thm_MIPStarRE_LDT_leftTensor_mul_rightTensor_eq_opTensor
import Theorems.Thm_MIPStarRE_LDT_opTensor_sub_left

set_option backward.isDefEq.respectTransparency false

/-!
# Phase-five endpoint for the evaluated-slice paper chain

This file isolates the paper line-87 removal endpoint and the finite
reindexing to the raw scalar `G`-commutativity stability defect.
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Paper-faithful phase-five removal after the right-register swap -/

/-- Paper line-87 endpoint after removing the trailing `G^x.total`.

At question `q = ((u,x),(v,y))` and outcome `(a,b)`, this is
`G^{u,x}_a G^{v,y}_b ⊗ A^{u,x}_a A^{v,y}_b`. -/
noncomputable def evaluatedSlicePhaseFivePaperRemoved
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (q : EvaluatedSliceQuestion params) : Error :=
  ∑ a : Fq params, ∑ b : Fq params,
    ev strategy.state
      (leftTensor (ι₂ := ι)
          (((evaluatedSliceFirstFactor params family q).outcome a) *
            ((evaluatedSliceSecondFactor params family q).outcome b)) *
        rightTensor (ι₁ := ι)
          (((evaluatedSlicePointMeas params strategy q.1).outcome a) *
            ((evaluatedSlicePointMeas params strategy q.2).outcome b)))

/-- Paper line 101 endpoint after reversing the first `eq:add-an-a` insertion. -/
noncomputable def evaluatedSlicePhaseSixFirstReverse
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (q : EvaluatedSliceQuestion params) : Error :=
  ∑ a : Fq params, ∑ b : Fq params,
    ev strategy.state
      (leftTensor (ι₂ := ι)
          (((evaluatedSliceFirstFactor params family q).outcome a) *
            ((evaluatedSliceFirstFactor params family q).outcome a) *
            ((evaluatedSliceSecondFactor params family q).outcome b)) *
        rightTensor (ι₁ := ι)
          ((evaluatedSlicePointMeas params strategy q.2).outcome b))

/-- Paper line 102 endpoint after simplifying the first-coordinate projector. -/
noncomputable def evaluatedSlicePhaseSixFirstRemoved
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (q : EvaluatedSliceQuestion params) : Error :=
  ∑ a : Fq params, ∑ b : Fq params,
    ev strategy.state
      (leftTensor (ι₂ := ι)
          (((evaluatedSliceFirstFactor params family q).outcome a) *
            ((evaluatedSliceSecondFactor params family q).outcome b)) *
        rightTensor (ι₁ := ι)
          ((evaluatedSlicePointMeas params strategy q.2).outcome b))

/-- Paper line 104 endpoint `eq:gonna-cite-this-in-just-a-bit`. -/
noncomputable def evaluatedSlicePhaseSevenGonnaCite
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (q : EvaluatedSliceQuestion params) : Error :=
  ∑ a : Fq params, ∑ b : Fq params,
    ev strategy.state
      (leftTensor (ι₂ := ι)
        (((evaluatedSliceFirstFactor params family q).outcome a) *
          ((evaluatedSliceSecondFactor params family q).outcome b) *
          ((evaluatedSliceSecondFactor params family q).outcome b)))

/-- Paper line 118 endpoint after moving the second factor to the right register. -/
noncomputable def evaluatedSlicePhaseEightTailRight
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (q : EvaluatedSliceQuestion params) : Error :=
  ∑ a : Fq params, ∑ b : Fq params,
    ev strategy.state
      (leftTensor (ι₂ := ι)
          (((evaluatedSliceFirstFactor params family q).outcome a) *
            ((evaluatedSliceSecondFactor params family q).outcome b)) *
        rightTensor (ι₁ := ι)
          ((evaluatedSliceSecondFactor params family q).outcome b))

/-- Ordered missing-mass defect for the paper phase-five removal.

This is the defect before swapping the two right-register point measurements:
`G^{u,x}_a G^{v,y}_b (1-G^x) ⊗ A^{u,x}_a A^{v,y}_b`. -/
noncomputable def evaluatedSlicePhaseFivePaperOrderedDefect
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (q : EvaluatedSliceQuestion params) : Error :=
  ∑ a : Fq params, ∑ b : Fq params,
    ev strategy.state
      (leftTensor (ι₂ := ι)
          (((evaluatedSliceFirstFactor params family q).outcome a) *
            ((evaluatedSliceSecondFactor params family q).outcome b) *
            (1 - (G (pointHeight params q.1)).total)) *
        rightTensor (ι₁ := ι)
          (((evaluatedSlicePointMeas params strategy q.1).outcome a) *
            ((evaluatedSlicePointMeas params strategy q.2).outcome b)))

/-- Swapped missing-mass defect for the paper phase-five removal.

After the right-register point swap, this reindexes to
`gCommStabilityTwoRawScalarDefect`: the right register is
`A^{v,y}_b A^{u,x}_a`. -/
noncomputable def evaluatedSlicePhaseFivePaperSwappedDefect
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (q : EvaluatedSliceQuestion params) : Error :=
  ∑ a : Fq params, ∑ b : Fq params,
    ev strategy.state
      (leftTensor (ι₂ := ι)
          (((evaluatedSliceFirstFactor params family q).outcome a) *
            ((evaluatedSliceSecondFactor params family q).outcome b) *
            (1 - (G (pointHeight params q.1)).total)) *
        rightTensor (ι₁ := ι)
          (((evaluatedSlicePointMeas params strategy q.2).outcome b) *
            ((evaluatedSlicePointMeas params strategy q.1).outcome a)))

/-- Pointwise algebra for the paper phase-five removal.

The swapped phase-four endpoint contains the left factor
`A_a B_b G^x.total`; subtracting the line-87 removed endpoint gives the negative
of the ordered defect `A_a B_b (1-G^x.total)`. -/
lemma evaluatedSlice_phaseFivePaper_term_diff
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (q : EvaluatedSliceQuestion params)
    (a b : Fq params) :
    ev strategy.state
        (leftTensor (ι₂ := ι)
            (((evaluatedSliceFirstFactor params family q).outcome a) *
              ((evaluatedSliceSecondFactor params family q).outcome b) *
              (evaluatedSliceFirstFactor params family q).total) *
          rightTensor (ι₁ := ι)
            (((evaluatedSlicePointMeas params strategy q.1).outcome a) *
              ((evaluatedSlicePointMeas params strategy q.2).outcome b))) -
      ev strategy.state
        (leftTensor (ι₂ := ι)
            (((evaluatedSliceFirstFactor params family q).outcome a) *
              ((evaluatedSliceSecondFactor params family q).outcome b)) *
          rightTensor (ι₁ := ι)
            (((evaluatedSlicePointMeas params strategy q.1).outcome a) *
              ((evaluatedSlicePointMeas params strategy q.2).outcome b))) =
    - ev strategy.state
        (leftTensor (ι₂ := ι)
            (((evaluatedSliceFirstFactor params family q).outcome a) *
              ((evaluatedSliceSecondFactor params family q).outcome b) *
              (1 - (G (pointHeight params q.1)).total)) *
          rightTensor (ι₁ := ι)
            (((evaluatedSlicePointMeas params strategy q.1).outcome a) *
              ((evaluatedSlicePointMeas params strategy q.2).outcome b))) := by
  have htotal : (evaluatedSliceFirstFactor params family q).total =
      (G (pointHeight params q.1)).total := by
    simpa [evaluatedSliceFirstFactor] using
      evaluatedPointFamily_total_eq_G_total params family G hG q.1
  let S : MIPStarRE.Quantum.Op ι :=
    ((evaluatedSliceFirstFactor params family q).outcome a) *
      ((evaluatedSliceSecondFactor params family q).outcome b)
  let T : MIPStarRE.Quantum.Op ι := (G (pointHeight params q.1)).total
  let P : MIPStarRE.Quantum.Op ι :=
    ((evaluatedSlicePointMeas params strategy q.1).outcome a) *
      ((evaluatedSlicePointMeas params strategy q.2).outcome b)
  change
    ev strategy.state
        (leftTensor (ι₂ := ι)
          (S * (evaluatedSliceFirstFactor params family q).total) *
        rightTensor (ι₁ := ι) P) -
      ev strategy.state (leftTensor (ι₂ := ι) S * rightTensor (ι₁ := ι) P) =
    - ev strategy.state (leftTensor (ι₂ := ι) (S * (1 - T)) * rightTensor (ι₁ := ι) P)
  rw [htotal]
  rw [← ev_sub]
  have hop :
      leftTensor (ι₂ := ι) (S * T) * rightTensor (ι₁ := ι) P -
          leftTensor (ι₂ := ι) S * rightTensor (ι₁ := ι) P =
        -(leftTensor (ι₂ := ι) (S * (1 - T)) * rightTensor (ι₁ := ι) P) := by
    calc
      leftTensor (ι₂ := ι) (S * T) * rightTensor (ι₁ := ι) P -
          leftTensor (ι₂ := ι) S * rightTensor (ι₁ := ι) P
        = opTensor (S * T) P - opTensor S P := by
            rw [leftTensor_mul_rightTensor_eq_opTensor,
              leftTensor_mul_rightTensor_eq_opTensor]
      _ = opTensor (S * T - S) P := by
            rw [MIPStarRE.LDT.opTensor_sub_left]
      _ = opTensor (-(S * (1 - T))) P := by
            have hs : S * T - S = -(S * (1 - T)) := by noncomm_ring
            rw [hs]
      _ = -(leftTensor (ι₂ := ι) (S * (1 - T)) * rightTensor (ι₁ := ι) P) := by
            have hneg : opTensor (-(S * (1 - T))) P = -(opTensor (S * (1 - T)) P) := by
              simpa [opTensor] using
                (Matrix.smul_kronecker (-1 : ℂ) (S * (1 - T)) P)
            rw [hneg]
            rw [leftTensor_mul_rightTensor_eq_opTensor]
  rw [hop]
  simpa using
    (ev_scale strategy.state (-1)
      (leftTensor (ι₂ := ι) (S * (1 - T)) * rightTensor (ι₁ := ι) P))

/-- Collapse the first-coordinate postprocessing fiber in the raw paper defect.

For fixed `(u,x)` and right prefix `P₂`, summing over evaluated outcomes `a`
expands `G^{u,x}_a = ∑_{g : g(u)=a} G^x_g` and collapses to a polynomial sum. -/
lemma phaseFivePaper_fiber_sum_ev
    (params : Parameters) [FieldModel params.q]
    (ψ : QuantumState (ι × ι))
    (u : Point params)
    (B T P₂ : MIPStarRE.Quantum.Op ι)
    (Gx : SubMeas (Polynomial params) ι)
    (P₁ : Fq params → MIPStarRE.Quantum.Op ι) :
    (∑ a : Fq params,
      ev ψ
        (leftTensor (ι₂ := ι)
            (((∑ g ∈ Finset.univ.filter
                    (fun g : Polynomial params => g u = a), Gx.outcome g) * B) * T) *
          rightTensor (ι₁ := ι) (P₂ * P₁ a))) =
      ∑ g : Polynomial params,
        ev ψ
          (leftTensor (ι₂ := ι) ((Gx.outcome g * B) * T) *
            rightTensor (ι₁ := ι) (P₂ * P₁ (g u))) := by
  classical
  calc
    ∑ a : Fq params,
        ev ψ
          (leftTensor (ι₂ := ι)
              (((∑ g ∈ Finset.univ.filter
                      (fun g : Polynomial params => g u = a), Gx.outcome g) * B) * T) *
            rightTensor (ι₁ := ι) (P₂ * P₁ a))
      = ∑ a : Fq params,
          ∑ g ∈ Finset.univ.filter (fun g : Polynomial params => g u = a),
            ev ψ
              (leftTensor (ι₂ := ι) (((1 : MIPStarRE.Quantum.Op ι) * Gx.outcome g * B) * T) *
                rightTensor (ι₁ := ι) (P₂ * P₁ a)) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          simpa [one_mul] using
            (ev_leftTensor_mul_middle_finset_sum (ι := ι)
              (s := Finset.univ.filter (fun g : Polynomial params => g u = a))
              (ψ := ψ) (A := (1 : MIPStarRE.Quantum.Op ι)) (C := B) (R := T)
              (D := P₂ * P₁ a) (B := fun g : Polynomial params => Gx.outcome g))
    _ = ∑ a : Fq params,
          ∑ g ∈ Finset.univ.filter (fun g : Polynomial params => g u = a),
            ev ψ
              (leftTensor (ι₂ := ι) (((1 : MIPStarRE.Quantum.Op ι) * Gx.outcome g * B) * T) *
                rightTensor (ι₁ := ι) (P₂ * P₁ (g u))) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          refine Finset.sum_congr rfl ?_
          intro g hg
          have hgu : g u = a := (Finset.mem_filter.mp hg).2
          simp [hgu]
    _ = ∑ g : Polynomial params,
          ev ψ
            (leftTensor (ι₂ := ι) (((1 : MIPStarRE.Quantum.Op ι) * Gx.outcome g * B) * T) *
              rightTensor (ι₁ := ι) (P₂ * P₁ (g u))) := by
          simpa using
            (Finset.sum_fiberwise Finset.univ (fun g : Polynomial params => g u)
              (fun g : Polynomial params =>
                ev ψ
                  (leftTensor (ι₂ := ι)
                    (((1 : MIPStarRE.Quantum.Op ι) * Gx.outcome g * B) * T) *
                    rightTensor (ι₁ := ι) (P₂ * P₁ (g u)))) )
    _ = ∑ g : Polynomial params,
          ev ψ
            (leftTensor (ι₂ := ι) ((Gx.outcome g * B) * T) *
              rightTensor (ι₁ := ι) (P₂ * P₁ (g u))) := by
          simp

/-- Pointwise expansion of the swapped paper defect after writing the first point as `(u,x)`.

The statement keeps point measurements in the local `evaluatedSlicePointMeas`
notation; the final reindexing lemma rewrites those to `strategy.pointMeasurement`
when matching `gCommStabilityTwoRawScalarDefect`. -/
lemma evaluatedSlicePhaseFivePaperSwappedDefect_appendPoint_expansion
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (x : Fq params) (u : Point params) (vy : Point params.next) :
    evaluatedSlicePhaseFivePaperSwappedDefect params strategy family G
        (appendPoint params u x, vy) =
      ∑ g : Polynomial params, ∑ b : Fq params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
              ((G x).outcome g *
                (evaluatedPointFamily params family vy).outcome b *
                (1 - (G x).total)) *
            rightTensor (ι₁ := ι)
              (((evaluatedSlicePointMeas params strategy vy).outcome b) *
                ((evaluatedSlicePointMeas params strategy
                    (appendPoint params u x)).outcome (g u)))) := by
  classical
  calc
    evaluatedSlicePhaseFivePaperSwappedDefect params strategy family G (appendPoint params u x, vy)
        = ∑ b : Fq params, ∑ g : Polynomial params,
            ev strategy.state
              (leftTensor (ι₂ := ι)
                  ((G x).outcome g *
                    (evaluatedPointFamily params family vy).outcome b *
                    (1 - (G x).total)) *
                rightTensor (ι₁ := ι)
                  (((evaluatedSlicePointMeas params strategy vy).outcome b) *
                    ((evaluatedSlicePointMeas params strategy (appendPoint params u x)).outcome
                      (g u)))) := by
          dsimp [evaluatedSlicePhaseFivePaperSwappedDefect, evaluatedSliceFirstFactor,
            evaluatedSliceSecondFactor]
          rw [pointHeight_appendPoint]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro b _
          have hfiber :=
            phaseFivePaper_fiber_sum_ev (ι := ι) params strategy.state u
              ((evaluatedPointFamily params family vy).outcome b)
              (1 - (G x).total)
              ((evaluatedSlicePointMeas params strategy vy).outcome b)
              (G x)
              (fun a : Fq params =>
                (evaluatedSlicePointMeas params strategy (appendPoint params u x)).outcome a)
          simpa [evaluatedPointFamily_appendPoint_outcome, hG, mul_assoc] using hfiber
    _ = ∑ g : Polynomial params, ∑ b : Fq params,
            ev strategy.state
              (leftTensor (ι₂ := ι)
                  ((G x).outcome g *
                    (evaluatedPointFamily params family vy).outcome b *
                    (1 - (G x).total)) *
                rightTensor (ι₁ := ι)
                  (((evaluatedSlicePointMeas params strategy vy).outcome b) *
                    ((evaluatedSlicePointMeas params strategy (appendPoint params u x)).outcome
                      (g u)))) := by
          rw [Finset.sum_comm]

end MIPStarRE.LDT.Commutativity


