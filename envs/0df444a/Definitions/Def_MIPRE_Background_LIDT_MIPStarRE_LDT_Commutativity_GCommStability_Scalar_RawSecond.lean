-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_GCommStability_Scalar_RawSecond
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_GCommStability_Scalar_RawSecond
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T03:39:59.596124+00:00
-- url     : https://prove2.me/theorems/6ee43254-34ca-4960-8dba-356a6c92d4fc
-- title:
--   Definitions of RawSecond: Section 11 commutativity: raw second scalar stability bound The raw uncollapsed form of the second scalar stability…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Commutativity.GCommStability.Scalar.RawSecond` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Section 11 commutativity: raw second scalar stability bound. The raw uncollapsed form of the second scalar stability estimate.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Definitions** (1): `MIPStarRE.LDT.Commutativity.gCommStabilityTwoRawScalarDefect` (Raw uncollapsed scalar defect for the paper's second `G`-commutativity stability estimate after the right-register point-product swap.).
--
--   **Embedded lemmas** (4): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `avgOver_right_linear`, `gCommStabilityTwo_raw_left_sum_le`, `gCommStabilityTwo_raw_scalar_pointwise_bound`, `sum_ev_leftTensor_mul_rightTensor_const`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Commutativity.GCommStability.Scalar.RawSecond` (`MIPRE/Background/LIDT/MIPStarRE/LDT/Commutativity/GCommStability/Scalar/RawSecond.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 44 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/Commutativity/GCommStability/Scalar/RawSecond.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Commutativity/GCommStability/Scalar/RawSecond.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Commutativity/GCommStability/Scalar/RawSecond.lean (definition bundle: declarations the uploaded statements rest on);
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
import Theorems.Thm_MIPStarRE_LDT_Commutativity_GCommStability_Scalar_averagedSlicePointEvaluationOperator_hermitian
import Theorems.Thm_MIPStarRE_LDT_Commutativity_GCommStability_Scalar_averagedSlicePointEvaluationOperator_sq_le_self
import Theorems.Thm_MIPStarRE_LDT_IdxPolyFamily_SliceBoundednessInput_averagedPoint_le_witness
import Theorems.Thm_MIPStarRE_LDT_Measurement_sum_eq
import Theorems.Thm_MIPStarRE_LDT_Preliminaries_projSubMeas_total_proj
import Theorems.Thm_MIPStarRE_LDT_Preliminaries_weightedFinsetCauchySchwarz
import Theorems.Thm_MIPStarRE_LDT_SubMeas_outcome_hermitian
import Theorems.Thm_MIPStarRE_LDT_SubMeas_total_nonneg
import Theorems.Thm_MIPStarRE_LDT_avgOver_mono
import Theorems.Thm_MIPStarRE_LDT_avgOver_uniform_const
import Theorems.Thm_MIPStarRE_LDT_ev_abs_mul_le_sqrt
import Theorems.Thm_MIPStarRE_LDT_ev_adjoint_self_nonneg
import Theorems.Thm_MIPStarRE_LDT_ev_finset_sum
import Theorems.Thm_MIPStarRE_LDT_ev_mono
import Theorems.Thm_MIPStarRE_LDT_ev_real_smul
import Theorems.Thm_MIPStarRE_LDT_leftTensor_finset_sum
import Theorems.Thm_MIPStarRE_LDT_leftTensor_le_one
import Theorems.Thm_MIPStarRE_LDT_leftTensor_mul_rightTensor_eq_opTensor
import Theorems.Thm_MIPStarRE_LDT_leftTensor_mul_rightTensor_real_smul_right
import Theorems.Thm_MIPStarRE_LDT_opTensor_mono_left
import Theorems.Thm_MIPStarRE_LDT_opTensor_mono_right
import Theorems.Thm_MIPStarRE_LDT_opTensor_mul
import Theorems.Thm_MIPStarRE_LDT_rightTensor_finset_sum
import Theorems.Thm_MIPStarRE_LDT_rightTensor_one
import Theorems.Thm_MIPStarRE_Quantum_kronecker_nonneg

set_option backward.isDefEq.respectTransparency false

/-!
# Section 11 commutativity: raw second scalar stability bound

The raw uncollapsed form of the second scalar stability estimate.
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open GCommStability.Scalar
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma avgOver_right_linear
    {U Γ Aidx : Type*} [Fintype Γ] [Fintype Aidx]
    (𝒟U : Distribution U)
    (ψ : QuantumState (ι × ι))
    (L : Γ → Aidx → MIPStarRE.Quantum.Op ι)
    (P : Aidx → MIPStarRE.Quantum.Op ι)
    (Q : U → Γ → MIPStarRE.Quantum.Op ι) :
    avgOver 𝒟U (fun u =>
      ∑ g : Γ, ∑ a : Aidx,
        ev ψ (leftTensor (ι₂ := ι) (L g a) *
          rightTensor (ι₁ := ι) (P a * Q u g))) =
    ∑ g : Γ, ∑ a : Aidx,
        ev ψ (leftTensor (ι₂ := ι) (L g a) *
          rightTensor (ι₁ := ι)
            (P a * averageOperatorOverDistribution 𝒟U (fun u => Q u g))) := by
  classical
  let T : U → Γ → Aidx → Error := fun u g a =>
    ev ψ (leftTensor (ι₂ := ι) (L g a) * rightTensor (ι₁ := ι) (P a * Q u g)) *
      𝒟U.weight u
  calc
    avgOver 𝒟U (fun u =>
      ∑ g : Γ, ∑ a : Aidx,
        ev ψ (leftTensor (ι₂ := ι) (L g a) *
          rightTensor (ι₁ := ι) (P a * Q u g)))
      = ∑ u ∈ 𝒟U.support, ∑ g : Γ, ∑ a : Aidx, T u g a := by
        simp [avgOver, T, Finset.mul_sum, mul_comm]
    _ = ∑ g : Γ, ∑ a : Aidx, ∑ u ∈ 𝒟U.support, T u g a := by
        calc
          ∑ u ∈ 𝒟U.support, ∑ g : Γ, ∑ a : Aidx, T u g a
            = ∑ g : Γ, ∑ u ∈ 𝒟U.support, ∑ a : Aidx, T u g a := by
              rw [Finset.sum_comm]
          _ = ∑ g : Γ, ∑ a : Aidx, ∑ u ∈ 𝒟U.support, T u g a := by
              refine Finset.sum_congr rfl ?_
              intro g _
              rw [Finset.sum_comm]
      _ = ∑ g : Γ, ∑ a : Aidx,
          ev ψ (leftTensor (ι₂ := ι) (L g a) *
            rightTensor (ι₁ := ι)
              (P a * averageOperatorOverDistribution 𝒟U (fun u => Q u g))) := by
          suffices
              ∑ g : Γ, ∑ a : Aidx, ∑ u ∈ 𝒟U.support,
                  ev ψ (leftTensor (ι₂ := ι) (L g a) *
                      rightTensor (ι₁ := ι) (P a * Q u g)) * 𝒟U.weight u =
                ∑ g : Γ, ∑ a : Aidx, ∑ u ∈ 𝒟U.support,
                  ev ψ ((𝒟U.weight u : Error) •
                    (leftTensor (ι₂ := ι) (L g a) *
                      rightTensor (ι₁ := ι) (P a * Q u g))) by
            simpa [T, averageOperatorOverDistribution, ev_finset_sum,
              ← rightTensor_finset_sum, leftTensor_mul_rightTensor_real_smul_right,
              Matrix.mul_sum] using this
          refine Finset.sum_congr rfl ?_
          intro g _
          refine Finset.sum_congr rfl ?_
          intro a _
          refine Finset.sum_congr rfl ?_
          intro u _
          let X : MIPStarRE.Quantum.Op (ι × ι) :=
            leftTensor (ι₂ := ι) (L g a) * rightTensor (ι₁ := ι) (P a * Q u g)
          change ev ψ X * 𝒟U.weight u = ev ψ ((𝒟U.weight u : Error) • X)
          rw [ev_real_smul]
          ring

lemma sum_ev_leftTensor_mul_rightTensor_const
    {α : Type*} (s : Finset α)
    (ψ : QuantumState (ι × ι))
    (L : α → MIPStarRE.Quantum.Op ι)
    (R : MIPStarRE.Quantum.Op ι) :
    ∑ a ∈ s, ev ψ (leftTensor (ι₂ := ι) (L a) * rightTensor (ι₁ := ι) R) =
      ev ψ (leftTensor (ι₂ := ι) (∑ a ∈ s, L a) * rightTensor (ι₁ := ι) R) := by
  classical
  calc
    ∑ a ∈ s, ev ψ (leftTensor (ι₂ := ι) (L a) * rightTensor (ι₁ := ι) R)
      = ev ψ ((∑ a ∈ s, leftTensor (ι₂ := ι) (L a)) * rightTensor (ι₁ := ι) R) := by
        simp [ev_finset_sum, Finset.sum_mul]
    _ = ev ψ (leftTensor (ι₂ := ι) (∑ a ∈ s, L a) * rightTensor (ι₁ := ι) R) := by
        rw [leftTensor_finset_sum]

/-- Raw uncollapsed scalar defect for the paper's second `G`-commutativity
stability estimate after the right-register point-product swap.

For fixed slice height `x`, this is the expression from
`commutativity-G.tex`, `clm:g-comm-stability2`, before collapsing the
`(v,y), b`-average into `gCommStabilityTwoR`.  The left register contains
`G^x_g B^{v,y}_b (1-G^x)`, while the right register contains the swapped point
product `P^{v,y}_b P^{u,x}_{g(u)}`. -/
noncomputable def gCommStabilityTwoRawScalarDefect
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (x : Fq params) : Error :=
  avgOver (uniformDistribution (Point params.next)) fun vy =>
    avgOver (uniformDistribution (Point params)) fun u =>
      ∑ g : Polynomial params, ∑ b : Fq params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
              ((G x).outcome g *
                (evaluatedPointFamily params family vy).outcome b *
                (1 - (G x).total)) *
            rightTensor (ι₁ := ι)
              (((strategy.pointMeasurement vy).toSubMeas.outcome b) *
                ((strategy.pointMeasurement (appendPoint params u x)).toSubMeas.outcome (g u))))

lemma gCommStabilityTwo_raw_left_sum_le
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (x : Fq params) (vy : Point params.next) :
    ∑ gb : Polynomial params × Fq params,
        ((1 - (G x).total) *
          ((evaluatedPointFamily params family vy).outcome gb.2 *
            (G x).outcome gb.1 *
            (evaluatedPointFamily params family vy).outcome gb.2) *
          (1 - (G x).total)) ≤
      1 - (G x).total := by
  classical
  let B : SubMeas (Fq params) ι := evaluatedPointFamily params family vy
  let T : MIPStarRE.Quantum.Op ι := (G x).total
  have hT_herm : Tᴴ = T := by
    exact
      (Matrix.nonneg_iff_posSemidef.mp <| by
        simpa [T] using (G x).total_nonneg).isHermitian.eq
  have hTc_herm : (1 - T)ᴴ = 1 - T := by simp [hT_herm]
  have hT_proj : T * T = T := by
    simpa [T, hG] using
      MIPStarRE.LDT.Preliminaries.projSubMeas_total_proj (family.meas x)
  have hinner_le :
      ∑ gb : Polynomial params × Fq params,
          B.outcome gb.2 * (G x).outcome gb.1 * B.outcome gb.2 ≤
        (1 : MIPStarRE.Quantum.Op ι) := by
    calc
      ∑ gb : Polynomial params × Fq params,
          B.outcome gb.2 * (G x).outcome gb.1 * B.outcome gb.2
        = ∑ b : Fq params, ∑ g : Polynomial params,
            B.outcome b * (G x).outcome g * B.outcome b := by
          calc
            ∑ gb : Polynomial params × Fq params,
                B.outcome gb.2 * (G x).outcome gb.1 * B.outcome gb.2
              = ∑ g : Polynomial params, ∑ b : Fq params,
                  B.outcome b * (G x).outcome g * B.outcome b := by
                rw [Fintype.sum_prod_type]
            _ = ∑ b : Fq params, ∑ g : Polynomial params,
                  B.outcome b * (G x).outcome g * B.outcome b := by
                rw [Finset.sum_comm]
      _ = ∑ b : Fq params, B.outcome b * T * B.outcome b := by
          refine Finset.sum_congr rfl ?_
          intro b _
          calc
            ∑ g : Polynomial params, B.outcome b * (G x).outcome g * B.outcome b
              = (∑ g : Polynomial params, B.outcome b * (G x).outcome g) * B.outcome b := by
                rw [Finset.sum_mul]
            _ = (B.outcome b * ∑ g : Polynomial params, (G x).outcome g) *
                  B.outcome b := by
                rw [Matrix.mul_sum]
            _ = B.outcome b * T * B.outcome b := by
                rw [(G x).sum_eq_total]
      _ ≤ ∑ b : Fq params, B.outcome b := by
          refine Finset.sum_le_sum ?_
          intro b _
          calc
            B.outcome b * T * B.outcome b ≤ B.outcome b * 1 * B.outcome b := by
              exact IsSelfAdjoint.conjugate_le_conjugate
                (G x).total_le_one (B.outcome_hermitian b)
            _ = B.outcome b := by
              simp [B, evaluatedPointFamily_outcome_proj params family vy b]
      _ = B.total := B.sum_eq_total
      _ ≤ 1 := B.total_le_one
  calc
    ∑ gb : Polynomial params × Fq params,
        ((1 - (G x).total) *
          ((evaluatedPointFamily params family vy).outcome gb.2 *
            (G x).outcome gb.1 *
            (evaluatedPointFamily params family vy).outcome gb.2) *
          (1 - (G x).total))
      = (1 - T) *
          (∑ gb : Polynomial params × Fq params,
            B.outcome gb.2 * (G x).outcome gb.1 * B.outcome gb.2) *
          (1 - T) := by
        simp [B, T, Matrix.mul_sum, Finset.sum_mul, mul_assoc]
    _ ≤ (1 - T) * 1 * (1 - T) := by
        exact IsSelfAdjoint.conjugate_le_conjugate hinner_le hTc_herm
    _ = 1 - T := by
        calc
          (1 - T) * 1 * (1 - T) = (1 - T) * (1 - T) := by simp
          _ = 1 - T - T + T * T := by noncomm_ring
          _ = 1 - T := by simp [hT_proj]

lemma gCommStabilityTwo_raw_scalar_pointwise_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta) :
    ∀ x : Fq params,
      |gCommStabilityTwoRawScalarDefect params strategy family G x| ≤
        Real.sqrt (hbound.storedResidual G x) := by
  classical
  intro x
  let 𝒟V : Distribution (Point params.next) := uniformDistribution (Point params.next)
  let 𝒟U : Distribution (Point params) := uniformDistribution (Point params)
  let T : MIPStarRE.Quantum.Op ι := (G x).total
  let W : Polynomial params → MIPStarRE.Quantum.Op ι :=
    IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x
  let X : Point params.next → Polynomial params × Fq params →
      MIPStarRE.Quantum.Op (ι × ι) := fun vy gb =>
    leftTensor (ι₂ := ι) ((G x).outcome gb.1) *
      rightTensor (ι₁ := ι) ((strategy.pointMeasurement vy).toSubMeas.outcome gb.2)
  let Y : Point params.next → Polynomial params × Fq params →
      MIPStarRE.Quantum.Op (ι × ι) := fun vy gb =>
    leftTensor (ι₂ := ι)
        ((G x).outcome gb.1 *
          (evaluatedPointFamily params family vy).outcome gb.2 * (1 - T)) *
      rightTensor (ι₁ := ι) (W gb.1)
  let xDiag : Point params.next → Polynomial params × Fq params → Error := fun vy gb =>
    ev strategy.state (X vy gb * (X vy gb)ᴴ)
  let yDiag : Point params.next → Polynomial params × Fq params → Error := fun vy gb =>
    ev strategy.state
      (leftTensor (ι₂ := ι)
          ((1 - T) *
            ((evaluatedPointFamily params family vy).outcome gb.2 *
              (G x).outcome gb.1 *
              (evaluatedPointFamily params family vy).outcome gb.2) *
            (1 - T)) *
        rightTensor (ι₁ := ι) (family.witness x))
  let t : Point params.next → Polynomial params × Fq params → Error := fun vy gb =>
    ev strategy.state
      (leftTensor (ι₂ := ι)
          ((G x).outcome gb.1 *
            (evaluatedPointFamily params family vy).outcome gb.2 * (1 - T)) *
        rightTensor (ι₁ := ι)
          (((strategy.pointMeasurement vy).toSubMeas.outcome gb.2) * W gb.1))
  have hraw_eq :
      gCommStabilityTwoRawScalarDefect params strategy family G x =
        avgOver 𝒟V (fun vy => ∑ gb : Polynomial params × Fq params, t vy gb) := by
    unfold gCommStabilityTwoRawScalarDefect
    change avgOver 𝒟V (fun vy =>
        avgOver 𝒟U (fun u =>
          ∑ g : Polynomial params, ∑ b : Fq params,
            ev strategy.state
              (leftTensor (ι₂ := ι)
                  ((G x).outcome g *
                    (evaluatedPointFamily params family vy).outcome b *
                    (1 - (G x).total)) *
                rightTensor (ι₁ := ι)
                  (((strategy.pointMeasurement vy).toSubMeas.outcome b) *
                    ((strategy.pointMeasurement
                      (appendPoint params u x)).toSubMeas.outcome (g u)))))) =
      avgOver 𝒟V (fun vy => ∑ gb : Polynomial params × Fq params, t vy gb)
    apply congrArg (avgOver 𝒟V)
    funext vy
    let L : Polynomial params → Fq params → MIPStarRE.Quantum.Op ι := fun g b =>
      (G x).outcome g * (evaluatedPointFamily params family vy).outcome b * (1 - (G x).total)
    let P : Fq params → MIPStarRE.Quantum.Op ι := fun b =>
      (strategy.pointMeasurement vy).toSubMeas.outcome b
    let Q : Point params → Polynomial params → MIPStarRE.Quantum.Op ι := fun u g =>
      (strategy.pointMeasurement (appendPoint params u x)).toSubMeas.outcome (g u)
    have hW :
        ∀ g : Polynomial params,
          averageOperatorOverDistribution 𝒟U (fun u => Q u g) = W g := by
      intro g
      try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal
    calc
      avgOver 𝒟U (fun u =>
          ∑ g : Polynomial params, ∑ b : Fq params,
            ev strategy.state
              (leftTensor (ι₂ := ι)
                  ((G x).outcome g *
                    (evaluatedPointFamily params family vy).outcome b *
                    (1 - (G x).total)) *
                rightTensor (ι₁ := ι)
                  (((strategy.pointMeasurement vy).toSubMeas.outcome b) *
                    ((strategy.pointMeasurement
                      (appendPoint params u x)).toSubMeas.outcome (g u)))))
        = ∑ g : Polynomial params, ∑ b : Fq params,
            ev strategy.state
              (leftTensor (ι₂ := ι) (L g b) *
                rightTensor (ι₁ := ι)
                  (P b * averageOperatorOverDistribution 𝒟U (fun u => Q u g))) := by
            simpa [L, P, Q] using
              (avgOver_right_linear (ι := ι) 𝒟U strategy.state L P Q)
      _ = ∑ gb : Polynomial params × Fq params, t vy gb := by
            rw [Fintype.sum_prod_type]
            refine Finset.sum_congr rfl ?_
            intro g _
            refine Finset.sum_congr rfl ?_
            intro b _
            rw [hW g]
  have hT_herm : Tᴴ = T := by
    exact
      (Matrix.nonneg_iff_posSemidef.mp <| by
        simpa [T] using (G x).total_nonneg).isHermitian.eq
  have hTc_herm : (1 - T)ᴴ = 1 - T := by simp [hT_herm]
  have hGproj : ∀ g : Polynomial params, (G x).outcome g * (G x).outcome g = (G x).outcome g := by
    intro g
    simpa [hG x] using (family.meas x).proj g
  have hX_expand : ∀ vy gb,
      X vy gb * (X vy gb)ᴴ =
        leftTensor (ι₂ := ι) ((G x).outcome gb.1) *
          rightTensor (ι₁ := ι) ((strategy.pointMeasurement vy).toSubMeas.outcome gb.2) := by
    intro vy gb
    have hG_herm : ((G x).outcome gb.1)ᴴ = (G x).outcome gb.1 :=
      (G x).outcome_hermitian gb.1
    have hP_herm : ((strategy.pointMeasurement vy).toSubMeas.outcome gb.2)ᴴ =
        (strategy.pointMeasurement vy).toSubMeas.outcome gb.2 :=
      ((strategy.pointMeasurement vy).toSubMeas.outcome_hermitian gb.2)
    have hP_proj : (strategy.pointMeasurement vy).toSubMeas.outcome gb.2 *
        (strategy.pointMeasurement vy).toSubMeas.outcome gb.2 =
        (strategy.pointMeasurement vy).toSubMeas.outcome gb.2 := by
      simpa using (strategy.pointMeasurement vy).proj gb.2
    calc
      X vy gb * (X vy gb)ᴴ
        = (opTensor ((G x).outcome gb.1)
            ((strategy.pointMeasurement vy).toSubMeas.outcome gb.2)) *
          (opTensor ((G x).outcome gb.1)
            ((strategy.pointMeasurement vy).toSubMeas.outcome gb.2))ᴴ := by
            simp [X, leftTensor_mul_rightTensor_eq_opTensor]
      _ = opTensor (((G x).outcome gb.1) * ((G x).outcome gb.1))
            (((strategy.pointMeasurement vy).toSubMeas.outcome gb.2) *
              ((strategy.pointMeasurement vy).toSubMeas.outcome gb.2)) := by
            rw [conjTranspose_opTensor, opTensor_mul]
            simp [hG_herm, hP_herm]
      _ = leftTensor (ι₂ := ι) ((G x).outcome gb.1) *
            rightTensor (ι₁ := ι) ((strategy.pointMeasurement vy).toSubMeas.outcome gb.2) := by
            rw [hGproj gb.1, hP_proj, leftTensor_mul_rightTensor_eq_opTensor]
  have hY_le : ∀ vy gb,
      ev strategy.state ((Y vy gb)ᴴ * Y vy gb) ≤ yDiag vy gb := by
    intro vy gb
    let B : MIPStarRE.Quantum.Op ι := (evaluatedPointFamily params family vy).outcome gb.2
    let Gg : MIPStarRE.Quantum.Op ι := (G x).outcome gb.1
    let Wg : MIPStarRE.Quantum.Op ι := W gb.1
    have hG_herm : Ggᴴ = Gg := by simpa [Gg] using (G x).outcome_hermitian gb.1
    have hB_herm : Bᴴ = B := by
      simpa [B] using (evaluatedPointFamily params family vy).outcome_hermitian gb.2
    have hW_herm : Wgᴴ = Wg := by
      simpa [Wg, W] using
        averagedSlicePointEvaluationOperator_hermitian params strategy x gb.1
    have hGg_proj : Gg * Gg = Gg := by
      simpa [Gg] using hGproj gb.1
    have hleft_alg :
        ((1 - T) * B * Gg) * (Gg * B * (1 - T)) =
          (1 - T) * (B * Gg * B) * (1 - T) := by
      calc
        ((1 - T) * B * Gg) * (Gg * B * (1 - T))
            = (1 - T) * B * (Gg * Gg) * B * (1 - T) := by noncomm_ring
        _ = (1 - T) * B * Gg * B * (1 - T) := by rw [hGg_proj]
        _ = (1 - T) * (B * Gg * B) * (1 - T) := by noncomm_ring
    have hY_expand :
        (Y vy gb)ᴴ * Y vy gb =
          leftTensor (ι₂ := ι) ((1 - T) * (B * Gg * B) * (1 - T)) *
            rightTensor (ι₁ := ι) (Wg * Wg) := by
      calc
        (Y vy gb)ᴴ * Y vy gb
          = (opTensor (Gg * B * (1 - T)) Wg)ᴴ *
              opTensor (Gg * B * (1 - T)) Wg := by
              simp [Y, Gg, B, Wg, leftTensor_mul_rightTensor_eq_opTensor]
        _ = opTensor (((Gg * B * (1 - T))ᴴ) * (Gg * B * (1 - T)))
              (Wgᴴ * Wg) := by
              rw [conjTranspose_opTensor, opTensor_mul]
        _ = opTensor (((1 - T) * B * Gg) * (Gg * B * (1 - T))) (Wg * Wg) := by
              simp [Matrix.conjTranspose_mul, hG_herm, hB_herm, hTc_herm, hW_herm,
                mul_assoc]
        _ = opTensor ((1 - T) * (B * Gg * B) * (1 - T)) (Wg * Wg) := by
              rw [hleft_alg]
        _ = leftTensor (ι₂ := ι) ((1 - T) * (B * Gg * B) * (1 - T)) *
              rightTensor (ι₁ := ι) (Wg * Wg) := by
              rw [leftTensor_mul_rightTensor_eq_opTensor]
    have hleft_pos : 0 ≤ (1 - T) * (B * Gg * B) * (1 - T) := by
      have hBGpos : 0 ≤ B * Gg * B := by
        exact IsSelfAdjoint.conjugate_nonneg (by simpa [Gg] using (G x).outcome_pos gb.1) hB_herm
      exact IsSelfAdjoint.conjugate_nonneg hBGpos hTc_herm
    have hWsq_le : Wg * Wg ≤ family.witness x := by
      calc
        Wg * Wg ≤ Wg := by
          simpa [Wg, W] using
            averagedSlicePointEvaluationOperator_sq_le_self params strategy x gb.1
        _ ≤ family.witness x := by
          simpa [Wg, W] using hbound.averagedPoint_le_witness x gb.1
    calc
      ev strategy.state ((Y vy gb)ᴴ * Y vy gb)
        = ev strategy.state
            (leftTensor (ι₂ := ι) ((1 - T) * (B * Gg * B) * (1 - T)) *
              rightTensor (ι₁ := ι) (Wg * Wg)) := by rw [hY_expand]
      _ ≤ ev strategy.state
            (leftTensor (ι₂ := ι) ((1 - T) * (B * Gg * B) * (1 - T)) *
              rightTensor (ι₁ := ι) (family.witness x)) := by
            exact ev_mono strategy.state _ _ <| by
              rw [leftTensor_mul_rightTensor_eq_opTensor,
                leftTensor_mul_rightTensor_eq_opTensor]
              exact MIPStarRE.LDT.opTensor_mono_right hleft_pos hWsq_le
      _ = yDiag vy gb := by
            simp [yDiag, B, Gg, T]
  have ht : ∀ vy gb, |t vy gb| ≤ Real.sqrt (xDiag vy gb) * Real.sqrt (yDiag vy gb) := by
    intro vy gb
    have hXY :
        X vy gb * Y vy gb =
          leftTensor (ι₂ := ι)
            ((G x).outcome gb.1 *
              (evaluatedPointFamily params family vy).outcome gb.2 * (1 - T)) *
            rightTensor (ι₁ := ι)
              (((strategy.pointMeasurement vy).toSubMeas.outcome gb.2) * W gb.1) := by
      calc
        X vy gb * Y vy gb
          = opTensor ((G x).outcome gb.1)
              ((strategy.pointMeasurement vy).toSubMeas.outcome gb.2) *
            opTensor
              ((G x).outcome gb.1 *
                (evaluatedPointFamily params family vy).outcome gb.2 * (1 - T))
              (W gb.1) := by
              simp [X, Y, leftTensor_mul_rightTensor_eq_opTensor]
        _ = opTensor
              (((G x).outcome gb.1 * (G x).outcome gb.1) *
                (evaluatedPointFamily params family vy).outcome gb.2 * (1 - T))
              (((strategy.pointMeasurement vy).toSubMeas.outcome gb.2) * W gb.1) := by
              rw [opTensor_mul]
              simp [mul_assoc]
        _ = leftTensor (ι₂ := ι)
              ((G x).outcome gb.1 *
                (evaluatedPointFamily params family vy).outcome gb.2 * (1 - T)) *
              rightTensor (ι₁ := ι)
                (((strategy.pointMeasurement vy).toSubMeas.outcome gb.2) * W gb.1) := by
              rw [hGproj gb.1, leftTensor_mul_rightTensor_eq_opTensor]
    have hbase := ev_abs_mul_le_sqrt strategy.state (X vy gb) (Y vy gb)
    calc
      |t vy gb| = |ev strategy.state (X vy gb * Y vy gb)| := by
        rw [hXY]
      _ ≤ Real.sqrt (xDiag vy gb) *
          Real.sqrt (ev strategy.state ((Y vy gb)ᴴ * Y vy gb)) := by
            simpa [xDiag] using hbase
      _ ≤ Real.sqrt (xDiag vy gb) * Real.sqrt (yDiag vy gb) := by
            exact mul_le_mul_of_nonneg_left
              (Real.sqrt_le_sqrt (hY_le vy gb)) (Real.sqrt_nonneg _)
  have hx : ∀ vy gb, 0 ≤ xDiag vy gb := by
    intro vy gb
    simpa [xDiag] using ev_adjoint_self_nonneg strategy.state ((X vy gb)ᴴ)
  have hy : ∀ vy gb, 0 ≤ yDiag vy gb := by
    intro vy gb
    let B : MIPStarRE.Quantum.Op ι := (evaluatedPointFamily params family vy).outcome gb.2
    let Gg : MIPStarRE.Quantum.Op ι := (G x).outcome gb.1
    have hB_herm : Bᴴ = B := by
      simpa [B] using (evaluatedPointFamily params family vy).outcome_hermitian gb.2
    have hleft_pos : 0 ≤ (1 - T) * (B * Gg * B) * (1 - T) := by
      have hBGpos : 0 ≤ B * Gg * B := by
        exact IsSelfAdjoint.conjugate_nonneg (by simpa [Gg] using (G x).outcome_pos gb.1) hB_herm
      exact IsSelfAdjoint.conjugate_nonneg hBGpos hTc_herm
    unfold yDiag
    apply ev_nonneg_of_psd
    rw [leftTensor_mul_rightTensor_eq_opTensor]
    simpa [B, Gg, T, opTensor] using
      MIPStarRE.Quantum.kronecker_nonneg hleft_pos (hbound.sliceOpPSD x)
  have hfirst_point : ∀ vy : Point params.next,
      ∑ gb : Polynomial params × Fq params, xDiag vy gb =
        ev strategy.state
          (leftTensor (ι₂ := ι) ((G x).total) *
            rightTensor (ι₁ := ι) (1 : MIPStarRE.Quantum.Op ι)) := by
    intro vy
    calc
      ∑ gb : Polynomial params × Fq params, xDiag vy gb
        = ∑ gb : Polynomial params × Fq params,
            ev strategy.state
              (leftTensor (ι₂ := ι) ((G x).outcome gb.1) *
                rightTensor (ι₁ := ι) ((strategy.pointMeasurement vy).toSubMeas.outcome gb.2)) := by
            refine Finset.sum_congr rfl ?_
            intro gb _
            change ev strategy.state (X vy gb * (X vy gb)ᴴ) =
              ev strategy.state
                (leftTensor (ι₂ := ι) ((G x).outcome gb.1) *
                  rightTensor (ι₁ := ι) ((strategy.pointMeasurement vy).toSubMeas.outcome gb.2))
            rw [hX_expand vy gb]
      _ = ∑ g : Polynomial params, ∑ b : Fq params,
            ev strategy.state
              (leftTensor (ι₂ := ι) ((G x).outcome g) *
                rightTensor (ι₁ := ι) ((strategy.pointMeasurement vy).toSubMeas.outcome b)) := by
            rw [Fintype.sum_prod_type]
      _ = ∑ g : Polynomial params,
            ev strategy.state
              (leftTensor (ι₂ := ι) ((G x).outcome g) *
                rightTensor (ι₁ := ι) (1 : MIPStarRE.Quantum.Op ι)) := by
            refine Finset.sum_congr rfl ?_
            intro g _
            calc
              ∑ b : Fq params,
                ev strategy.state
                  (leftTensor (ι₂ := ι) ((G x).outcome g) *
                    rightTensor (ι₁ := ι) ((strategy.pointMeasurement vy).toSubMeas.outcome b))
                = ev strategy.state
                    (leftTensor (ι₂ := ι) ((G x).outcome g) *
                      rightTensor (ι₁ := ι)
                        (∑ b : Fq params, (strategy.pointMeasurement vy).outcome b)) := by
                    simp [ev_finset_sum, ← rightTensor_finset_sum, Finset.mul_sum]
              _ = ev strategy.state
                    (leftTensor (ι₂ := ι) ((G x).outcome g) *
                      rightTensor (ι₁ := ι) (1 : MIPStarRE.Quantum.Op ι)) := by
                    have hsumP :
                        (∑ b : Fq params, (strategy.pointMeasurement vy).outcome b) =
                          (1 : MIPStarRE.Quantum.Op ι) := by
                      exact (strategy.pointMeasurement vy).toMeasurement.sum_eq
                    rw [hsumP]
      _ = ev strategy.state
            (leftTensor (ι₂ := ι) ((G x).total) *
              rightTensor (ι₁ := ι) (1 : MIPStarRE.Quantum.Op ι)) := by
            calc
              ∑ g : Polynomial params,
                ev strategy.state
                  (leftTensor (ι₂ := ι) ((G x).outcome g) *
                    rightTensor (ι₁ := ι) (1 : MIPStarRE.Quantum.Op ι))
                = ev strategy.state
                    ((∑ g : Polynomial params, leftTensor (ι₂ := ι) ((G x).outcome g)) *
                      rightTensor (ι₁ := ι) (1 : MIPStarRE.Quantum.Op ι)) := by
                    simp [ev_finset_sum, Finset.sum_mul]
              _ = ev strategy.state
                  (leftTensor (ι₂ := ι) ((G x).total) *
                    rightTensor (ι₁ := ι) (1 : MIPStarRE.Quantum.Op ι)) := by
                    rw [leftTensor_finset_sum (ι₂ := ι) Finset.univ
                      (fun g : Polynomial params => (G x).outcome g), (G x).sum_eq_total]
  have hfirst : avgOver 𝒟V (fun vy => ∑ gb : Polynomial params × Fq params, xDiag vy gb) ≤ 1 := by
    calc
      avgOver 𝒟V (fun vy => ∑ gb : Polynomial params × Fq params, xDiag vy gb)
        = ev strategy.state
            (leftTensor (ι₂ := ι) ((G x).total) *
              rightTensor (ι₁ := ι) (1 : MIPStarRE.Quantum.Op ι)) := by
            calc
              avgOver 𝒟V (fun vy => ∑ gb : Polynomial params × Fq params, xDiag vy gb)
                = avgOver 𝒟V (fun _ : Point params.next =>
                    ev strategy.state
                      (leftTensor (ι₂ := ι) ((G x).total) *
                        rightTensor (ι₁ := ι) (1 : MIPStarRE.Quantum.Op ι))) := by
                    apply congrArg (avgOver 𝒟V)
                    funext vy
                    exact hfirst_point vy
              _ = ev strategy.state
                    (leftTensor (ι₂ := ι) ((G x).total) *
                      rightTensor (ι₁ := ι) (1 : MIPStarRE.Quantum.Op ι)) := by
                    simpa [𝒟V] using
                      (avgOver_uniform_const (α := Point params.next)
                        (ev strategy.state
                          (leftTensor (ι₂ := ι) ((G x).total) *
                            rightTensor (ι₁ := ι) (1 : MIPStarRE.Quantum.Op ι))))
      _ ≤ ev strategy.state (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
            exact ev_mono strategy.state _ _ <| by
              rw [rightTensor_one (ι₁ := ι) (ι₂ := ι), mul_one]
              exact leftTensor_le_one (ι₂ := ι) (G x).total_le_one
      _ = 1 := ev_one_of_isNormalized strategy.state hnorm
  have hsecond_point : ∀ vy : Point params.next,
      (∑ gb : Polynomial params × Fq params, yDiag vy gb) ≤ hbound.storedResidual G x := by
    intro vy
    calc
      ∑ gb : Polynomial params × Fq params, yDiag vy gb
        = ev strategy.state
            (leftTensor (ι₂ := ι)
              (∑ gb : Polynomial params × Fq params,
                ((1 - (G x).total) *
                  ((evaluatedPointFamily params family vy).outcome gb.2 *
                    (G x).outcome gb.1 *
                    (evaluatedPointFamily params family vy).outcome gb.2) *
                  (1 - (G x).total))) *
              rightTensor (ι₁ := ι) (family.witness x)) := by
            simpa [yDiag, T] using
              (sum_ev_leftTensor_mul_rightTensor_const
                (ι := ι) (Finset.univ : Finset (Polynomial params × Fq params))
                strategy.state
                (fun gb : Polynomial params × Fq params =>
                  ((1 - (G x).total) *
                    ((evaluatedPointFamily params family vy).outcome gb.2 *
                      (G x).outcome gb.1 *
                      (evaluatedPointFamily params family vy).outcome gb.2) *
                    (1 - (G x).total)))
                (family.witness x))
      _ ≤ ev strategy.state
            (leftTensor (ι₂ := ι) (1 - (G x).total) *
              rightTensor (ι₁ := ι) (family.witness x)) := by
            exact ev_mono strategy.state _ _ <| by
              rw [leftTensor_mul_rightTensor_eq_opTensor,
                leftTensor_mul_rightTensor_eq_opTensor]
              exact opTensor_mono_left
                (gCommStabilityTwo_raw_left_sum_le params family G hG x vy)
                (hbound.sliceOpPSD x)
      _ = hbound.storedResidual G x := rfl
  have hsecond :
      avgOver 𝒟V (fun vy => ∑ gb : Polynomial params × Fq params, yDiag vy gb) ≤
        hbound.storedResidual G x := by
    calc
      avgOver 𝒟V (fun vy => ∑ gb : Polynomial params × Fq params, yDiag vy gb)
        ≤ avgOver 𝒟V (fun _ : Point params.next => hbound.storedResidual G x) := by
            exact avgOver_mono 𝒟V _ _ hsecond_point
      _ = hbound.storedResidual G x := by
            simpa [𝒟V] using
              (avgOver_uniform_const (α := Point params.next) (hbound.storedResidual G x))
  have hcs :=
    MIPStarRE.LDT.Preliminaries.weightedFinsetCauchySchwarz
      (𝒟 := 𝒟V) (t := t) (x := xDiag) (y := yDiag) ht hx hy
  calc
    |gCommStabilityTwoRawScalarDefect params strategy family G x|
      = |avgOver 𝒟V (fun vy => ∑ gb : Polynomial params × Fq params, t vy gb)| := by
          rw [hraw_eq]
    _ ≤
        Real.sqrt (avgOver 𝒟V
          (fun vy => ∑ gb : Polynomial params × Fq params, xDiag vy gb)) *
          Real.sqrt (avgOver 𝒟V
            (fun vy => ∑ gb : Polynomial params × Fq params, yDiag vy gb)) := hcs
    _ ≤ Real.sqrt 1 * Real.sqrt (hbound.storedResidual G x) := by
          apply mul_le_mul
          · exact Real.sqrt_le_sqrt hfirst
          · exact Real.sqrt_le_sqrt hsecond
          · exact Real.sqrt_nonneg _
          · exact Real.sqrt_nonneg _
    _ = Real.sqrt (hbound.storedResidual G x) := by simp

end MIPStarRE.LDT.Commutativity


