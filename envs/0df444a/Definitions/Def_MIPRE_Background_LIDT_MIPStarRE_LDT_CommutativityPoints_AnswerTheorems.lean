-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_CommutativityPoints_AnswerTheorems
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_CommutativityPoints_AnswerTheorems
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T03:45:17.514171+00:00
-- url     : https://prove2.me/theorems/f92dfc07-c8f3-4572-b72d-66c3b37b42bc
-- title:
--   Definitions of AnswerTheorems: Section 10 commutativity points: answer-valued diagonal measurements This file proves the commutativity-at-points…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.CommutativityPoints.AnswerTheorems` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Section 10 commutativity points: answer-valued diagonal measurements. This file proves the commutativity-at-points theorem using the answer-valued diagonal-line verifier relation. The conclusion concerns only the point measurements, hence it can later be transferred to the ordinary carrier used by self-improvement, but the proof does not use the carrier's inert diagonal measurement.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Definitions** (10): `MIPStarRE.LDT.CommutativityPoints.answerPointMeasurementProductLeft` (The ordered point product `(A^u_a A^v_b) ⊗ I` for an answer-valued strategy.); `MIPStarRE.LDT.CommutativityPoints.answerPointMeasurementProductRight` (The reversed point product `(A^v_b A^u_a) ⊗ I` for an answer-valued strategy.); `MIPStarRE.LDT.CommutativityPoints.answerSampledDiagonalLineEvaluation` (Evaluate an answer-valued diagonal-line measurement at the sampled parameter.); `MIPStarRE.LDT.CommutativityPoints.answerSampledPointMeasurement` (The point measurement, reindexed by a sampled diagonal line and a parameter on it, for an answer-valued strategy.); `_private.MIPRE.Background.LIDT.MIPStarRE.LDT.CommutativityPoints.AnswerTheorems.0.MIPStarRE.LDT.CommutativityPoints.answerDiagonalLineProductOrdered`; `_private.MIPRE.Background.LIDT.MIPStarRE.LDT.CommutativityPoints.AnswerTheorems.0.MIPStarRE.LDT.CommutativityPoints.answerDiagonalLineProductReversed`; `_private.MIPRE.Background.LIDT.MIPStarRE.LDT.CommutativityPoints.AnswerTheorems.0.MIPStarRE.LDT.CommutativityPoints.answerPointDiagonalLineMixedProductLeft`; `_private.MIPRE.Background.LIDT.MIPStarRE.LDT.CommutativityPoints.AnswerTheorems.0.MIPStarRE.LDT.CommutativityPoints.answerPointDiagonalLineMixedProductRight`; `_private.MIPRE.Background.LIDT.MIPStarRE.LDT.CommutativityPoints.AnswerTheorems.0.MIPStarRE.LDT.CommutativityPoints.answerPointMeasurementProductAlongSharedLine`; and -1 more.
--
--   **Embedded lemmas** (8): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `answerOrderedDropFromLineComparison`, `answerOrderedLiftToLineProduct`, `answerOrderedLiftToMixedLine`, `answerPointDiagonalLineMixedProductLeft_outcome`, `answerPointDiagonalLineMixedProductRight_outcome`, `answerReversedDropToPointsComparison`, `answerSampledDiagonalLineApproximation_ignore_first`, `answerSampledDiagonalLineApproximation_ignore_second`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.CommutativityPoints.AnswerTheorems` (`MIPRE/Background/LIDT/MIPStarRE/LDT/CommutativityPoints/AnswerTheorems.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 34 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/CommutativityPoints/AnswerTheorems.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/CommutativityPoints/AnswerTheorems.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/CommutativityPoints/AnswerTheorems.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_CommutativityPoints_Approximation
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_CommutativityPoints_SharedHelpers_SharedLine
import Theorems.Thm_MIPStarRE_LDT_CommutativityPoints_answer_sampledDiagonalLineApproximation_pointWithDiagonalLine
import Theorems.Thm_MIPStarRE_LDT_CommutativityPoints_avgOver_pointPairSharedDiagonalLine_ignore_first
import Theorems.Thm_MIPStarRE_LDT_CommutativityPoints_avgOver_pointPairSharedDiagonalLine_ignore_second
import Theorems.Thm_MIPStarRE_LDT_CommutativityPoints_liftLeft_mul_leftPlaced_outcome
import Theorems.Thm_MIPStarRE_LDT_CommutativityPoints_liftLeft_mul_rightPlaced_outcome
import Theorems.Thm_MIPStarRE_LDT_CommutativityPoints_liftRight_mul_leftPlaced_outcome
import Theorems.Thm_MIPStarRE_LDT_CommutativityPoints_liftRight_mul_rightPlaced_outcome
import Theorems.Thm_MIPStarRE_LDT_CommutativityPoints_sddOpRel_congr_outcome
import Theorems.Thm_MIPStarRE_LDT_CommutativityPoints_sddOpRel_reindex
import Theorems.Thm_MIPStarRE_LDT_CommutativityPoints_sddOpRel_symm
import Theorems.Thm_MIPStarRE_LDT_CommutativityPoints_subMeas_sum_adjoint_mul_le_one
import Theorems.Thm_MIPStarRE_LDT_Preliminaries_cabApproxDelta_raw
import Theorems.Thm_MIPStarRE_LDT_ProjMeas_postprocess_outcome_commute
import Theorems.Thm_MIPStarRE_LDT_SubMeas_total_nonneg
import Theorems.Thm_MIPStarRE_LDT_avgOver_congr
import Theorems.Thm_MIPStarRE_LDT_leftTensor_le_one
import Theorems.Thm_MIPStarRE_LDT_leftTensor_mul_rightTensor_eq_opTensor
import Theorems.Thm_MIPStarRE_LDT_opTensor_le_leftTensor

set_option backward.isDefEq.respectTransparency false
/-!
# Section 10 commutativity points: answer-valued diagonal measurements
This file proves the commutativity-at-points theorem using the answer-valued
diagonal-line verifier relation.  The conclusion concerns only the point
measurements, hence it can later be transferred to the ordinary carrier used by
self-improvement, but the proof does not use the carrier's inert diagonal
measurement.
## References
- `references/ldt-paper/commutativity-points.tex`
-/

namespace MIPStarRE.LDT.CommutativityPoints

open MIPStarRE.LDT.GlobalVariance (PointPairQuestion)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped Matrix MatrixOrder ComplexOrder BigOperators

/-- The point measurement, reindexed by a sampled diagonal line and a parameter
on it, for an answer-valued strategy. -/
def answerSampledPointMeasurement
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι) :
    IdxSubMeas (PointDiagonalLineQuestion params) (Fq params) ι :=
  fun q =>
    (strategy.pointMeasurement (sampledPointFromDiagonalQuestion params q)).toSubMeas

/-- Evaluate an answer-valued diagonal-line measurement at the sampled
parameter. -/
noncomputable def answerSampledDiagonalLineEvaluation
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι) :
    IdxSubMeas (PointDiagonalLineQuestion params) (Fq params) ι :=
  fun q =>
    postprocess ((strategy.diagonalMeasurement q.1).toSubMeas) (fun f => f q.2)

/-- The ordered point product `(A^u_a A^v_b) ⊗ I` for an answer-valued
strategy. -/
noncomputable def answerPointMeasurementProductLeft
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι) :
    IdxOpFamily (PointPairQuestion params) (PointPairOutcome params) (ι × ι) :=
  fun uv =>
    let Au := (strategy.pointMeasurement uv.1).toSubMeas
    let Av := (strategy.pointMeasurement uv.2).toSubMeas
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      orderedProductOpFamily Au Av

/-- The reversed point product `(A^v_b A^u_a) ⊗ I` for an answer-valued
strategy. -/
noncomputable def answerPointMeasurementProductRight
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι) :
    IdxOpFamily (PointPairQuestion params) (PointPairOutcome params) (ι × ι) :=
  fun uv =>
    let Au := (strategy.pointMeasurement uv.1).toSubMeas
    let Av := (strategy.pointMeasurement uv.2).toSubMeas
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      reversedProductOpFamily Au Av

noncomputable def answerPointMeasurementProductAlongSharedLine
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι) :
    IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
  fun q =>
    answerPointMeasurementProductLeft params strategy
      (sampledPointPairFromSharedDiagonalQuestion params q)

noncomputable def answerPointMeasurementProductAlongSharedLineReversed
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι) :
    IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
  fun q =>
    answerPointMeasurementProductRight params strategy
      (sampledPointPairFromSharedDiagonalQuestion params q)

noncomputable def answerPointDiagonalLineMixedProductLeft
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι) :
    IdxSubMeas (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
  fun q =>
    let ℓ := q.1
    let tu := q.2.1
    let tv := q.2.2
    let Au := (strategy.pointMeasurement (ℓ.pointAt tu)).toSubMeas
    let Lv := answerSampledDiagonalLineEvaluation params strategy (ℓ, tv)
    tensorProductSubMeas Au Lv

noncomputable def answerDiagonalLineProductOrdered
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι) :
    IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
  fun q =>
    let ℓ := q.1
    let tu := q.2.1
    let tv := q.2.2
    let Lu := answerSampledDiagonalLineEvaluation params strategy (ℓ, tu)
    let Lv := answerSampledDiagonalLineEvaluation params strategy (ℓ, tv)
    OpFamily.rightPlacedOpFamily (ιA := ι) <|
      reversedProductOpFamily Lu Lv

noncomputable def answerDiagonalLineProductReversed
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι) :
    IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
  fun q =>
    let ℓ := q.1
    let tu := q.2.1
    let tv := q.2.2
    let Lu := answerSampledDiagonalLineEvaluation params strategy (ℓ, tu)
    let Lv := answerSampledDiagonalLineEvaluation params strategy (ℓ, tv)
    OpFamily.rightPlacedOpFamily (ιA := ι) <|
      orderedProductOpFamily Lu Lv

noncomputable def answerPointDiagonalLineMixedProductRight
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι) :
    IdxSubMeas (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
  fun q =>
    let ℓ := q.1
    let tu := q.2.1
    let tv := q.2.2
    let Av := (strategy.pointMeasurement (ℓ.pointAt tv)).toSubMeas
    let Lu := answerSampledDiagonalLineEvaluation params strategy (ℓ, tu)
    postprocess (tensorProductSubMeas Av Lu) Prod.swap

lemma answerPointDiagonalLineMixedProductLeft_outcome
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι)
    (q : PointPairDiagonalLineQuestion params)
    (a b : Fq params) :
    ((IdxSubMeas.toIdxOpFamily
        (answerPointDiagonalLineMixedProductLeft params strategy) q).outcome (a, b)) =
      opTensor
        ((strategy.pointMeasurement (q.1.pointAt q.2.1)).outcome a)
        ((answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).outcome b) := by
  simp [answerPointDiagonalLineMixedProductLeft, tensorProductSubMeas,
    answerSampledDiagonalLineEvaluation, IdxSubMeas.toIdxOpFamily, SubMeas.toOpFamily,
    leftTensor_mul_rightTensor_eq_opTensor]

lemma answerPointDiagonalLineMixedProductRight_outcome
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι)
    (q : PointPairDiagonalLineQuestion params)
    (a b : Fq params) :
    ((IdxSubMeas.toIdxOpFamily
        (answerPointDiagonalLineMixedProductRight params strategy) q).outcome (a, b)) =
      opTensor
        ((strategy.pointMeasurement (q.1.pointAt q.2.2)).outcome b)
        ((answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome a) := by
  classical
  suffices h :
      ∑ ab : Fq params × Fq params with ab.2 = a ∧ ab.1 = b,
        opTensor ((strategy.pointMeasurement (q.1.pointAt q.2.2)).outcome ab.1)
          ((answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome ab.2) =
      opTensor ((strategy.pointMeasurement (q.1.pointAt q.2.2)).outcome b)
        ((answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome a) by
    simpa [answerPointDiagonalLineMixedProductRight, tensorProductSubMeas,
      postprocess, Prod.swap, IdxSubMeas.toIdxOpFamily, SubMeas.toOpFamily,
      leftTensor_mul_rightTensor_eq_opTensor] using h
  have hfilter :
      (Finset.univ.filter (fun ab : Fq params × Fq params => ab.2 = a ∧ ab.1 = b)) =
        {(b, a)} := by
    ext ab
    rcases ab with ⟨a', b'⟩
    simp [and_comm]
  rw [hfilter]
  simp

lemma answerSampledDiagonalLineApproximation_ignore_first
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    SDDOpRel strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (fun q =>
        OpFamily.leftPlacedOpFamily (ιB := ι)
          ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas))
      (fun q =>
        OpFamily.rightPlacedOpFamily (ιA := ι)
          (SubMeas.toOpFamily (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2))))
      (pointDiagonalLineApproxError params gamma) := by
  rcases answer_sampledDiagonalLineApproximation_pointWithDiagonalLine
    params strategy eps delta gamma hgood with ⟨happrox⟩
  constructor
  calc
    sddErrorOp strategy.state
        (pointPairSharedDiagonalLineDistribution params)
        (fun q =>
          OpFamily.leftPlacedOpFamily (ιB := ι)
            ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas))
        (fun q =>
          OpFamily.rightPlacedOpFamily (ιA := ι)
            (SubMeas.toOpFamily
              (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2))))
      = avgOver (pointPairSharedDiagonalLineDistribution params)
          (fun q =>
            qSDD strategy.state
              ((IdxSubMeas.liftLeft (answerSampledPointMeasurement params strategy))
                (q.1, q.2.2))
              ((IdxSubMeas.liftRight (answerSampledDiagonalLineEvaluation params strategy))
                (q.1, q.2.2))) := by
            unfold sddErrorOp
            apply avgOver_congr
            intro q
            unfold qSDDOp qSDD qSDDCore IdxSubMeas.liftLeft IdxSubMeas.liftRight
              OpFamily.leftPlacedOpFamily OpFamily.rightPlacedOpFamily
              answerSampledPointMeasurement sampledPointFromDiagonalQuestion
              answerSampledDiagonalLineEvaluation SubMeas.toOpFamily
            try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal
    _ = avgOver (pointWithDiagonalLineDistribution params)
          (fun q =>
            qSDD strategy.state
              ((IdxSubMeas.liftLeft (answerSampledPointMeasurement params strategy)) q)
              ((IdxSubMeas.liftRight
                (answerSampledDiagonalLineEvaluation params strategy)) q)) := by
            exact avgOver_pointPairSharedDiagonalLine_ignore_first params
              (fun q =>
                qSDD strategy.state
                  ((IdxSubMeas.liftLeft (answerSampledPointMeasurement params strategy)) q)
                  ((IdxSubMeas.liftRight
                    (answerSampledDiagonalLineEvaluation params strategy)) q))
    _ = sddError strategy.state
          (pointWithDiagonalLineDistribution params)
          (IdxSubMeas.liftLeft (answerSampledPointMeasurement params strategy))
          (IdxSubMeas.liftRight (answerSampledDiagonalLineEvaluation params strategy)) := by
            try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal
    _ ≤ pointDiagonalLineApproxError params gamma := by
          change
            sddError strategy.state (pointWithDiagonalLineDistribution params)
              (IdxSubMeas.liftLeft
                (fun q : PointDiagonalLineQuestion params =>
                  (strategy.pointMeasurement (q.1.pointAt q.2)).toSubMeas))
              (IdxSubMeas.liftRight
                (fun q : PointDiagonalLineQuestion params =>
                  postprocess (strategy.diagonalMeasurement.toIdxProjMeas q.1).toSubMeas
                    (fun f => f q.2))) ≤ pointDiagonalLineApproxError params gamma
          exact happrox

lemma answerSampledDiagonalLineApproximation_ignore_second
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    SDDOpRel strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (fun q =>
        OpFamily.leftPlacedOpFamily (ιB := ι)
          ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas))
      (fun q =>
        OpFamily.rightPlacedOpFamily (ιA := ι)
          (SubMeas.toOpFamily (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1))))
      (pointDiagonalLineApproxError params gamma) := by
  rcases answer_sampledDiagonalLineApproximation_pointWithDiagonalLine
    params strategy eps delta gamma hgood with ⟨happrox⟩
  constructor
  calc
    sddErrorOp strategy.state
        (pointPairSharedDiagonalLineDistribution params)
        (fun q =>
          OpFamily.leftPlacedOpFamily (ιB := ι)
            ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas))
        (fun q =>
          OpFamily.rightPlacedOpFamily (ιA := ι)
            (SubMeas.toOpFamily
              (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1))))
      = avgOver (pointPairSharedDiagonalLineDistribution params)
          (fun q =>
            qSDD strategy.state
              ((IdxSubMeas.liftLeft (answerSampledPointMeasurement params strategy))
                (q.1, q.2.1))
              ((IdxSubMeas.liftRight (answerSampledDiagonalLineEvaluation params strategy))
                (q.1, q.2.1))) := by
            unfold sddErrorOp
            apply avgOver_congr
            intro q
            unfold qSDDOp qSDD qSDDCore IdxSubMeas.liftLeft IdxSubMeas.liftRight
              OpFamily.leftPlacedOpFamily OpFamily.rightPlacedOpFamily
              answerSampledPointMeasurement sampledPointFromDiagonalQuestion
              answerSampledDiagonalLineEvaluation SubMeas.toOpFamily
            try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal
    _ = avgOver (pointWithDiagonalLineDistribution params)
          (fun q =>
            qSDD strategy.state
              ((IdxSubMeas.liftLeft (answerSampledPointMeasurement params strategy)) q)
              ((IdxSubMeas.liftRight
                (answerSampledDiagonalLineEvaluation params strategy)) q)) := by
            exact avgOver_pointPairSharedDiagonalLine_ignore_second params
              (fun q =>
                qSDD strategy.state
                  ((IdxSubMeas.liftLeft (answerSampledPointMeasurement params strategy)) q)
                  ((IdxSubMeas.liftRight
                    (answerSampledDiagonalLineEvaluation params strategy)) q))
    _ = sddError strategy.state
          (pointWithDiagonalLineDistribution params)
          (IdxSubMeas.liftLeft (answerSampledPointMeasurement params strategy))
          (IdxSubMeas.liftRight (answerSampledDiagonalLineEvaluation params strategy)) := by
            try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal
    _ ≤ pointDiagonalLineApproxError params gamma := by
          change
            sddError strategy.state (pointWithDiagonalLineDistribution params)
              (IdxSubMeas.liftLeft
                (fun q : PointDiagonalLineQuestion params =>
                  (strategy.pointMeasurement (q.1.pointAt q.2)).toSubMeas))
              (IdxSubMeas.liftRight
                (fun q : PointDiagonalLineQuestion params =>
                  postprocess (strategy.diagonalMeasurement.toIdxProjMeas q.1).toSubMeas
                    (fun f => f q.2))) ≤ pointDiagonalLineApproxError params gamma
          exact happrox

/-- **Lean-only:** A local tensor-placement comparison in the answer-valued
point-commutativity chain.

Paper origin: `references/ldt-paper/commutativity_points.tex`; this is one of
the formal transport steps used to realize the mixed point/diagonal comparison
appearing in the paper.  It is internal to the answer-valued implementation
tracked in issue #1507 and is not a source theorem.  Discharge: proved here from
the already formalized point-to-diagonal-line approximation and tensor-ordering
identities. -/
lemma answerOrderedLiftToMixedLine
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    SDDOpRel strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (answerPointMeasurementProductAlongSharedLine params strategy)
      (IdxSubMeas.toIdxOpFamily (answerPointDiagonalLineMixedProductLeft params strategy))
      (pointDiagonalLineApproxError params gamma) := by
  let e := pointPairOutcomeSwapEquiv params
  let Araw : IdxOpFamily (PointPairDiagonalLineQuestion params) (Fq params × Fq params) (ι × ι) :=
    fun q =>
      let Au := (strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas
      let Av := (strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas
      opFamilyOfOutcome fun ab : PointPairOutcome params =>
        (Au.liftLeft).outcome ab.2 *
          (OpFamily.leftPlacedOpFamily (ιB := ι) Av).outcome ab.1
  let Braw : IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
    fun q =>
      let Au := (strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas
      let Lv := answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2)
      opFamilyOfOutcome fun ab : PointPairOutcome params =>
        (Au.liftLeft).outcome ab.2 *
          (OpFamily.rightPlacedOpFamily (ιA := ι) Lv.toOpFamily).outcome ab.1
  let hbase :=
    answerSampledDiagonalLineApproximation_ignore_first params strategy eps delta gamma hgood
  let hcab :=
    MIPStarRE.LDT.Preliminaries.cabApproxDelta_raw
      strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (fun q =>
        OpFamily.leftPlacedOpFamily (ιB := ι)
          ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas))
      (fun q =>
        OpFamily.rightPlacedOpFamily (ιA := ι)
          (SubMeas.toOpFamily (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2))))
      (fun q _b a =>
        (((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas).liftLeft).outcome a)
      (pointDiagonalLineApproxError params gamma)
      hbase
      (by
        intro q b
        exact subMeas_sum_adjoint_mul_le_one
          (((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas).liftLeft))
  have hreindexed :=
    sddOpRel_reindex e strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      Araw
      Braw
      (pointDiagonalLineApproxError params gamma)
      hcab
  let Astep :
      IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
    fun q =>
      ({ outcome := fun ab : PointPairOutcome params => (Araw q).outcome (e.symm ab)
         total := (Araw q).total } : OpFamily (PointPairOutcome params) (ι × ι))
  let Bstep :
      IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
    fun q =>
      ({ outcome := fun ab : PointPairOutcome params => (Braw q).outcome (e.symm ab)
         total := (Braw q).total } : OpFamily (PointPairOutcome params) (ι × ι))
  exact sddOpRel_congr_outcome strategy.state
    (pointPairSharedDiagonalLineDistribution params)
    Astep Bstep
    (answerPointMeasurementProductAlongSharedLine params strategy)
    (IdxSubMeas.toIdxOpFamily (answerPointDiagonalLineMixedProductLeft params strategy))
    (pointDiagonalLineApproxError params gamma)
    (by
      intro q ab
      rcases ab with ⟨a, b⟩
      calc
        (Astep q).outcome (a, b)
          = leftTensor
              ((strategy.pointMeasurement (q.1.pointAt q.2.1)).outcome a *
                (strategy.pointMeasurement (q.1.pointAt q.2.2)).outcome b) := by
                  simpa [Astep, Araw, e, opFamilyOfOutcome,
                    pointPairOutcomeSwapEquiv] using
                    liftLeft_mul_leftPlaced_outcome
                      ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas)
                      ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas)
                      a b
        _ = (answerPointMeasurementProductAlongSharedLine params strategy q).outcome (a, b) := by
              symm
              simp [answerPointMeasurementProductAlongSharedLine, answerPointMeasurementProductLeft,
                orderedProductOpFamily, sampledPointPairFromSharedDiagonalQuestion,
                OpFamily.leftPlacedOpFamily])
    (by
      intro q ab
      rcases ab with ⟨a, b⟩
      calc
        (Bstep q).outcome (a, b)
          = opTensor
              ((strategy.pointMeasurement (q.1.pointAt q.2.1)).outcome a)
              ((answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).outcome b) := by
                  simpa [Bstep, Braw, e, opFamilyOfOutcome,
                    pointPairOutcomeSwapEquiv] using
                    liftLeft_mul_rightPlaced_outcome
                      ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas)
                      (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2))
                      a b
        _ =
            ((IdxSubMeas.toIdxOpFamily
                (answerPointDiagonalLineMixedProductLeft params strategy)) q).outcome
              (a, b) := by
              symm
              exact answerPointDiagonalLineMixedProductLeft_outcome params strategy q a b)
    hreindexed

/-- **Lean-only:** A local tensor-placement comparison from the mixed product to
the ordered diagonal-line product.

Paper origin: `references/ldt-paper/commutativity_points.tex`; this is an
internal reindexing and tensor-ordering step in the answer-valued
point-commutativity route tracked in issue #1507.  Discharge: proved here by
transporting the point-to-line comparison through the explicit ordered product
identities. -/
lemma answerOrderedLiftToLineProduct
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    SDDOpRel strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (IdxSubMeas.toIdxOpFamily (answerPointDiagonalLineMixedProductLeft params strategy))
      (answerDiagonalLineProductOrdered params strategy)
      (pointDiagonalLineApproxError params gamma) := by
  let Araw : IdxOpFamily (PointPairDiagonalLineQuestion params) (Fq params × Fq params)
      (ι × ι) :=
    fun q =>
      let Lv := answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2)
      ({ outcome := fun ab : Fq params × Fq params =>
           opTensor
             ((strategy.pointMeasurement (q.1.pointAt q.2.1)).outcome ab.1)
             (Lv.outcome ab.2)
         total := ∑ ab : Fq params × Fq params,
           opTensor
             ((strategy.pointMeasurement (q.1.pointAt q.2.1)).outcome ab.1)
             (Lv.outcome ab.2)
       } : OpFamily (Fq params × Fq params) (ι × ι))
  let Braw : IdxOpFamily (PointPairDiagonalLineQuestion params) (Fq params × Fq params)
      (ι × ι) :=
    fun q =>
      let Lu := answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1)
      let Lv := answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2)
      ({ outcome := fun ab : Fq params × Fq params =>
           rightTensor (Lv.outcome ab.2 * Lu.outcome ab.1)
         total := ∑ ab : Fq params × Fq params,
           rightTensor (Lv.outcome ab.2 * Lu.outcome ab.1)
       } : OpFamily (Fq params × Fq params) (ι × ι))
  let hbase :=
    answerSampledDiagonalLineApproximation_ignore_second params strategy eps delta gamma hgood
  have hcab :=
    MIPStarRE.LDT.Preliminaries.cabApproxDelta_raw
      strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (fun q =>
        OpFamily.leftPlacedOpFamily (ιB := ι)
          ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas))
      (fun q =>
        OpFamily.rightPlacedOpFamily (ιA := ι)
          (SubMeas.toOpFamily (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1))))
      (fun q _a b =>
        ((answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).liftRight).outcome b)
      (pointDiagonalLineApproxError params gamma)
      hbase
      (by
        intro q a
        exact subMeas_sum_adjoint_mul_le_one
          ((answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).liftRight))
  let Astep : IdxOpFamily (PointPairDiagonalLineQuestion params) (Fq params × Fq params)
      (ι × ι) :=
    fun q =>
      let Au := (strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas
      let Lv := answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2)
      ({ outcome := fun ab : Fq params × Fq params =>
           (Lv.liftRight).outcome ab.2 *
             (OpFamily.leftPlacedOpFamily (ιB := ι) Au).outcome ab.1
         total := ∑ ab : Fq params × Fq params,
           (Lv.liftRight).outcome ab.2 *
             (OpFamily.leftPlacedOpFamily (ιB := ι) Au).outcome ab.1
       } : OpFamily (Fq params × Fq params) (ι × ι))
  let Bstep : IdxOpFamily (PointPairDiagonalLineQuestion params) (Fq params × Fq params)
      (ι × ι) :=
    fun q =>
      let Lu := answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1)
      let Lv := answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2)
      ({ outcome := fun ab : Fq params × Fq params =>
           (Lv.liftRight).outcome ab.2 *
             (OpFamily.rightPlacedOpFamily (ιA := ι) (SubMeas.toOpFamily Lu)).outcome ab.1
         total := ∑ ab : Fq params × Fq params,
           (Lv.liftRight).outcome ab.2 *
             (OpFamily.rightPlacedOpFamily (ιA := ι) (SubMeas.toOpFamily Lu)).outcome ab.1
       } : OpFamily (Fq params × Fq params) (ι × ι))
  exact sddOpRel_congr_outcome strategy.state
    (pointPairSharedDiagonalLineDistribution params)
    Astep Bstep
    (IdxSubMeas.toIdxOpFamily (answerPointDiagonalLineMixedProductLeft params strategy))
    (answerDiagonalLineProductOrdered params strategy)
    (pointDiagonalLineApproxError params gamma)
    (by
      intro q ab
      rcases ab with ⟨a, b⟩
      calc
        (Astep q).outcome (a, b)
          = opTensor
              ((strategy.pointMeasurement (q.1.pointAt q.2.1)).outcome a)
              ((answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).outcome b) := by
                  simpa [Astep] using
                    liftRight_mul_leftPlaced_outcome
                      (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2))
                      ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas)
                      b a
        _ =
            ((IdxSubMeas.toIdxOpFamily
                (answerPointDiagonalLineMixedProductLeft params strategy)) q).outcome
              (a, b) := by
              symm
              exact answerPointDiagonalLineMixedProductLeft_outcome params strategy q a b)
    (by
      intro q ab
      rcases ab with ⟨a, b⟩
      calc
        (Bstep q).outcome (a, b)
          = rightTensor
              ((answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).outcome b *
                (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome a) := by
                  simpa [Bstep] using
                    liftRight_mul_rightPlaced_outcome
                      (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2))
                      (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1))
                      b a
        _ = (answerDiagonalLineProductOrdered params strategy q).outcome (a, b) := by
              symm
              simp [answerDiagonalLineProductOrdered, answerSampledDiagonalLineEvaluation,
                OpFamily.rightPlacedOpFamily, reversedProductOpFamily])
    hcab

/-- **Lean-only:** A local tensor-placement comparison from the ordered
diagonal-line product to the reversed mixed product.

Paper origin: `references/ldt-paper/commutativity_points.tex`; this is an
internal answer-valued implementation step for the point-commutativity argument
tracked in issue #1507.  Discharge: proved here from the reversed
point-to-line comparison and the explicit ordered/reversed product equality. -/
lemma answerOrderedDropFromLineComparison
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    SDDOpRel strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (answerDiagonalLineProductOrdered params strategy)
      (IdxSubMeas.toIdxOpFamily (answerPointDiagonalLineMixedProductRight params strategy))
      (pointDiagonalLineApproxError params gamma) := by
  have hrev :
      SDDOpRel strategy.state
        (pointPairSharedDiagonalLineDistribution params)
        (answerDiagonalLineProductReversed params strategy)
        (IdxSubMeas.toIdxOpFamily (answerPointDiagonalLineMixedProductRight params strategy))
        (pointDiagonalLineApproxError params gamma) := by
    let e := pointPairOutcomeSwapEquiv params
    let Araw : IdxOpFamily (PointPairDiagonalLineQuestion params) (Fq params × Fq params)
        (ι × ι) :=
      fun q =>
        let Lu := answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1)
        let Lv := answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2)
        opFamilyOfOutcome fun ab : PointPairOutcome params =>
          (Lu.liftRight).outcome ab.2 *
            (OpFamily.rightPlacedOpFamily (ιA := ι) Lv.toOpFamily).outcome ab.1
    let Braw : IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params)
        (ι × ι) :=
      fun q =>
        let Lu := answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1)
        let Av := (strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas
        opFamilyOfOutcome fun ab : PointPairOutcome params =>
          (Lu.liftRight).outcome ab.2 *
            (OpFamily.leftPlacedOpFamily (ιB := ι) Av).outcome ab.1
    let hbase :=
      sddOpRel_symm strategy.state
        (pointPairSharedDiagonalLineDistribution params)
        (fun q =>
          OpFamily.leftPlacedOpFamily (ιB := ι)
            ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas))
        (fun q =>
          OpFamily.rightPlacedOpFamily (ιA := ι)
            (SubMeas.toOpFamily
              (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2))))
        (pointDiagonalLineApproxError params gamma)
        (answerSampledDiagonalLineApproximation_ignore_first params strategy eps delta gamma hgood)
    let hcab :=
      MIPStarRE.LDT.Preliminaries.cabApproxDelta_raw
        strategy.state
        (pointPairSharedDiagonalLineDistribution params)
        (fun q =>
          OpFamily.rightPlacedOpFamily (ιA := ι)
            (SubMeas.toOpFamily
              (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2))))
        (fun q =>
          OpFamily.leftPlacedOpFamily (ιB := ι)
            ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas))
        (fun q _b a =>
          ((answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).liftRight).outcome a)
        (pointDiagonalLineApproxError params gamma)
        hbase
        (by
          intro q b
          exact subMeas_sum_adjoint_mul_le_one
            ((answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).liftRight))
    have hreindexed :=
      sddOpRel_reindex e strategy.state
        (pointPairSharedDiagonalLineDistribution params)
        Araw
        Braw
        (pointDiagonalLineApproxError params gamma)
        hcab
    let Astep :
        IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
      fun q =>
        ({ outcome := fun ab : PointPairOutcome params => (Araw q).outcome (e.symm ab)
           total := (Araw q).total } : OpFamily (PointPairOutcome params) (ι × ι))
    let Bstep :
        IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
      fun q =>
        ({ outcome := fun ab : PointPairOutcome params => (Braw q).outcome (e.symm ab)
           total := (Braw q).total } : OpFamily (PointPairOutcome params) (ι × ι))
    exact sddOpRel_congr_outcome strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      Astep Bstep
      (answerDiagonalLineProductReversed params strategy)
      (IdxSubMeas.toIdxOpFamily (answerPointDiagonalLineMixedProductRight params strategy))
      (pointDiagonalLineApproxError params gamma)
      (by
        intro q ab
        rcases ab with ⟨a, b⟩
        calc
          (Astep q).outcome (a, b)
            = rightTensor
                ((answerSampledDiagonalLineEvaluation params strategy
                    (q.1, q.2.1)).outcome a *
                  (answerSampledDiagonalLineEvaluation params strategy
                    (q.1, q.2.2)).outcome b) := by
                    simpa [Astep, Araw, e, opFamilyOfOutcome,
                      pointPairOutcomeSwapEquiv] using
                      liftRight_mul_rightPlaced_outcome
                        (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1))
                        (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.2))
                        a b
          _ = (answerDiagonalLineProductReversed params strategy q).outcome (a, b) := by
                symm
                simp [answerDiagonalLineProductReversed, answerSampledDiagonalLineEvaluation,
                  OpFamily.rightPlacedOpFamily, orderedProductOpFamily])
      (by
        intro q ab
        rcases ab with ⟨a, b⟩
        calc
          (Bstep q).outcome (a, b)
            = opTensor
                ((strategy.pointMeasurement (q.1.pointAt q.2.2)).outcome b)
                ((answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome a) := by
                    simpa [Bstep, Braw, e, opFamilyOfOutcome,
                      pointPairOutcomeSwapEquiv] using
                      liftRight_mul_leftPlaced_outcome
                        (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1))
                        ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas)
                        a b
          _ =
              ((IdxSubMeas.toIdxOpFamily
                  (answerPointDiagonalLineMixedProductRight params strategy)) q).outcome
                (a, b) := by
                symm
                exact answerPointDiagonalLineMixedProductRight_outcome params strategy q a b)
      hreindexed
  exact sddOpRel_congr_outcome strategy.state
    (pointPairSharedDiagonalLineDistribution params)
    (answerDiagonalLineProductReversed params strategy)
    (IdxSubMeas.toIdxOpFamily (answerPointDiagonalLineMixedProductRight params strategy))
    (answerDiagonalLineProductOrdered params strategy)
    (IdxSubMeas.toIdxOpFamily (answerPointDiagonalLineMixedProductRight params strategy))
    (pointDiagonalLineApproxError params gamma)
    (by
      intro q ⟨a, b⟩
      symm
      simp only [answerDiagonalLineProductOrdered, answerDiagonalLineProductReversed,
        OpFamily.rightPlacedOpFamily, reversedProductOpFamily, orderedProductOpFamily,
        answerSampledDiagonalLineEvaluation]
      congr 1
      exact (strategy.diagonalMeasurement q.1).postprocess_outcome_commute
        (fun f => f q.2.2) (fun f => f q.2.1) b a)
    (by intro q ab; rfl)
    hrev

/-- **Lean-only:** A local tensor-placement comparison from the reversed mixed
product back to the reversed point product.

Paper origin: `references/ldt-paper/commutativity_points.tex`; this is the last
internal answer-valued transport step in the point-commutativity chain tracked
in issue #1507.  Discharge: proved here from the line-to-point comparison and
the explicit tensor-placement identities. -/
lemma answerReversedDropToPointsComparison
    (params : Parameters)
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    SDDOpRel strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (IdxSubMeas.toIdxOpFamily (answerPointDiagonalLineMixedProductRight params strategy))
      (answerPointMeasurementProductAlongSharedLineReversed params strategy)
      (pointDiagonalLineApproxError params gamma) := by
  let Astep : IdxOpFamily (PointPairDiagonalLineQuestion params) (Fq params × Fq params)
      (ι × ι) :=
    fun q =>
      let Av := (strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas
      let Lu := answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1)
      ({ outcome := fun ab : Fq params × Fq params =>
           (Av.liftLeft).outcome ab.2 *
             (OpFamily.rightPlacedOpFamily (ιA := ι) (SubMeas.toOpFamily Lu)).outcome ab.1
         total := ∑ ab : Fq params × Fq params,
           (Av.liftLeft).outcome ab.2 *
             (OpFamily.rightPlacedOpFamily (ιA := ι) (SubMeas.toOpFamily Lu)).outcome ab.1
       } : OpFamily (Fq params × Fq params) (ι × ι))
  let Bstep : IdxOpFamily (PointPairDiagonalLineQuestion params) (Fq params × Fq params)
      (ι × ι) :=
    fun q =>
      let Au := (strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas
      let Av := (strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas
      ({ outcome := fun ab : Fq params × Fq params =>
           (Av.liftLeft).outcome ab.2 *
             (OpFamily.leftPlacedOpFamily (ιB := ι) Au).outcome ab.1
         total := ∑ ab : Fq params × Fq params,
           (Av.liftLeft).outcome ab.2 *
             (OpFamily.leftPlacedOpFamily (ιB := ι) Au).outcome ab.1
       } : OpFamily (Fq params × Fq params) (ι × ι))
  let hbase :=
    sddOpRel_symm strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (fun q =>
        OpFamily.leftPlacedOpFamily (ιB := ι)
          ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas))
      (fun q =>
        OpFamily.rightPlacedOpFamily (ιA := ι)
          (SubMeas.toOpFamily (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1))))
      (pointDiagonalLineApproxError params gamma)
      (answerSampledDiagonalLineApproximation_ignore_second params strategy eps delta gamma hgood)
  have hcab :=
    MIPStarRE.LDT.Preliminaries.cabApproxDelta_raw
      strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (fun q =>
        OpFamily.rightPlacedOpFamily (ιA := ι)
          (SubMeas.toOpFamily (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1))))
      (fun q =>
        OpFamily.leftPlacedOpFamily (ιB := ι)
          ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas))
      (fun q _a b =>
        (((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas).liftLeft).outcome b)
      (pointDiagonalLineApproxError params gamma)
      hbase
      (by
        intro q a
        exact subMeas_sum_adjoint_mul_le_one
          (((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas).liftLeft))
  exact sddOpRel_congr_outcome strategy.state
    (pointPairSharedDiagonalLineDistribution params)
    Astep Bstep
    (IdxSubMeas.toIdxOpFamily (answerPointDiagonalLineMixedProductRight params strategy))
    (answerPointMeasurementProductAlongSharedLineReversed params strategy)
    (pointDiagonalLineApproxError params gamma)
    (by
      intro q ab
      rcases ab with ⟨a, b⟩
      calc
        (Astep q).outcome (a, b)
          = opTensor
              ((strategy.pointMeasurement (q.1.pointAt q.2.2)).outcome b)
              ((answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome a) := by
                  simpa [Astep] using
                    liftLeft_mul_rightPlaced_outcome
                      ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas)
                      (answerSampledDiagonalLineEvaluation params strategy (q.1, q.2.1))
                      b a
        _ =
            ((IdxSubMeas.toIdxOpFamily
                (answerPointDiagonalLineMixedProductRight params strategy)) q).outcome
              (a, b) := by
              symm
              exact answerPointDiagonalLineMixedProductRight_outcome params strategy q a b)
    (by
      intro q ab
      rcases ab with ⟨a, b⟩
      calc
        (Bstep q).outcome (a, b)
          = leftTensor
              ((strategy.pointMeasurement (q.1.pointAt q.2.2)).outcome b *
                (strategy.pointMeasurement (q.1.pointAt q.2.1)).outcome a) := by
                  simpa [Bstep] using
                    liftLeft_mul_leftPlaced_outcome
                      ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas)
                      ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas)
                      b a
        _ = (answerPointMeasurementProductAlongSharedLineReversed params strategy q).outcome
              (a, b) := by
              symm
              simp [answerPointMeasurementProductAlongSharedLineReversed,
                answerPointMeasurementProductRight, reversedProductOpFamily,
                sampledPointPairFromSharedDiagonalQuestion, OpFamily.leftPlacedOpFamily])
    hcab

end MIPStarRE.LDT.CommutativityPoints


